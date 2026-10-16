package rardecode

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"crypto/hmac"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"errors"
	"hash/crc32"
	"io"
	"io/fs"
	"testing"
	"time"
)

// ---- BLAKE2sp known answer tests (official unkeyed vectors) ----

func TestBLAKE2spKAT(t *testing.T) {
	vectors := []struct {
		in  string // hex
		out string
	}{
		{"", "dd0e891776933f43c7d032b08a917e25741f8aa9a12c12e1cac8801500f2ca4f"},
		{"00", "a6b9eecc25227ad788c99d3f236debc8da408849e9a5178978727a81457f7239"},
		{"0001", "dacadece7a8e6bf3abfe324ca695436984b8195d29f6bbd896e41e18e21c9145"},
		{"0001020304", "2bb6333729000be3d5a21b98f8e7ead077f151a5393919eb67c876ee00bbbb04"},
	}
	for _, v := range vectors {
		in, err := hex.DecodeString(v.in)
		if err != nil {
			t.Fatal(err)
		}
		want, err := hex.DecodeString(v.out)
		if err != nil {
			t.Fatal(err)
		}
		h := newBlake2sp()
		if _, err := h.Write(in); err != nil {
			t.Fatal(err)
		}
		if got := h.Sum(nil); !bytes.Equal(got, want) {
			t.Fatalf("blake2sp(%x):\n got %x\nwant %x", in, got, want)
		}
		if len(in) == 0 {
			if got := newBlake2sp().Sum(nil); !bytes.Equal(got, want) {
				t.Fatalf("blake2sp(empty): got %x want %x", got, want)
			}
		}
	}
}

// TestBLAKE2spChunked checks that the result is independent of how the
// input is split across Write calls, notably around 512 byte stripes.
func TestBLAKE2spChunked(t *testing.T) {
	data := bytes.Repeat([]byte("rardecode-blake2sp-"), 100) // 2000 bytes
	expected := blake2Sum(data)
	for _, chunk := range []int{1, 3, 7, 63, 64, 65, 255, 511, 512, 513, 2000} {
		h := newBlake2sp()
		for i := 0; i < len(data); {
			n := min(chunk, len(data)-i)
			h.Write(data[i : i+n])
			i += n
		}
		if got := h.Sum(nil); !bytes.Equal(got, expected) {
			t.Fatalf("chunk size %d mismatch:\n got %x\nwant %x", chunk, got, expected)
		}
	}
}

// ---- RAR 5.0 archive construction helpers ----

func encVint(n uint64) []byte {
	var b []byte
	for n >= 0x80 {
		b = append(b, byte(n)|0x80)
		n >>= 7
	}
	return append(b, byte(n))
}

// rar5Block wraps a header body and optional data area with the header
// CRC32 and size fields.
func rar5Block(body, data []byte) []byte {
	hdr := encVint(uint64(len(body)))
	hdr = append(hdr, body...)
	out := make([]byte, 0, 4+len(hdr)+len(data))
	out = binary.LittleEndian.AppendUint32(out, crc32.ChecksumIEEE(hdr))
	out = append(out, hdr...)
	out = append(out, data...)
	return out
}

var rar5Signature = []byte{0x52, 0x61, 0x72, 0x21, 0x1a, 0x07, 0x01, 0x00}

func rar5ArcHeader(multi bool, volnum int) []byte {
	body := []byte{block5Arc, 0}
	arcFlags := byte(0)
	if multi {
		arcFlags |= 0x01
	}
	if volnum > 0 {
		arcFlags |= 0x02
	}
	body = append(body, arcFlags)
	if volnum > 0 {
		body = append(body, encVint(uint64(volnum-1))...)
	}
	return rar5Block(body, nil)
}

func rar5EndHeader(notLast bool) []byte {
	body := []byte{block5End, 0} // type, no data, no extras
	if notLast {
		body = append(body, endArc5NotLast)
	} else {
		body = append(body, 0)
	}
	return rar5Block(body, nil)
}

// hashExtra builds a type 2 file hash extra record. When raw is non-nil it
// is used verbatim as the record payload after the record type.
func hashExtra(htype uint64, hashData, raw []byte) []byte {
	rec := []byte{file5ExtraHash}
	if raw != nil {
		rec = append(rec, raw...)
	} else {
		rec = append(rec, encVint(htype)...)
		rec = append(rec, hashData...)
	}
	return append(encVint(uint64(len(rec))), rec...)
}

// cryptExtra builds a type 1 file encryption extra record.
func cryptExtra(kdfCount byte, salt, iv, check []byte, useMac bool) []byte {
	rec := []byte{file5ExtraCrypt, 0} // record type, version 0
	flags := byte(0)
	if check != nil {
		flags |= file5ExtraCryptCheckPresent
	}
	if useMac {
		flags |= file5ExtraCryptUseMac
	}
	rec = append(rec, flags, kdfCount)
	rec = append(rec, salt...)
	rec = append(rec, iv...)
	if check != nil {
		rec = append(rec, check...)
	}
	return append(encVint(uint64(len(rec))), rec...)
}

func blake2Sum(p []byte) []byte {
	h := newBlake2sp()
	_, _ = h.Write(p)
	return h.Sum(nil)
}

func crc32LE(p []byte) []byte {
	s := crc32.ChecksumIEEE(p)
	return []byte{byte(s), byte(s >> 8), byte(s >> 16), byte(s >> 24)}
}

func macDigest(key, sum []byte) []byte {
	mac := hmac.New(sha256.New, key)
	_, _ = mac.Write(sum)
	return mac.Sum(nil)
}

type rar5Part struct {
	first, last bool
	data        []byte // packed data for this part
	unpSize     uint64 // whole file unpacked size
	compInfo    uint64 // compression information vint (0 == stored)
	hasCRC      bool
	crcDigest   []byte // CRC declared inline by this part (nil -> derive)
	extras      []byte // extra area (file hash and encryption records)
}

// rar5FileHeader builds one file header block for a file part. whole is the
// complete unpacked file, used only to derive a whole-file inline CRC32 for
// the last part; other digests (notably BLAKE2sp) arrive as extra records.
func rar5FileHeader(name string, p rar5Part, whole []byte) []byte {
	crcDeclared := p.crcDigest
	if crcDeclared == nil && p.hasCRC {
		if p.last {
			crcDeclared = crc32LE(whole)
		} else {
			crcDeclared = crc32LE(p.data)
		}
	}

	var flags uint64 = block5HasData
	if len(p.extras) > 0 {
		flags |= block5HasExtra
	}
	if !p.first {
		flags |= block5DataNotFirst
	}
	if !p.last {
		flags |= block5DataNotLast
	}

	var fileFlags uint64
	if p.hasCRC {
		fileFlags |= file5HasCRC32
	}

	var body []byte
	body = append(body, block5File)
	body = append(body, encVint(flags)...)
	if flags&block5HasExtra > 0 {
		body = append(body, encVint(uint64(len(p.extras)))...)
	}
	body = append(body, encVint(uint64(len(p.data)))...)
	body = append(body, encVint(fileFlags)...)
	body = append(body, encVint(p.unpSize)...)
	body = append(body, encVint(0x20)...) // attributes
	if fileFlags&file5HasCRC32 > 0 {
		body = append(body, crcDeclared...)
	}
	body = append(body, encVint(p.compInfo)...)
	body = append(body, file5HostOSUnix)
	body = append(body, encVint(uint64(len(name)))...)
	body = append(body, name...)
	body = append(body, p.extras...)
	return rar5Block(body, p.data)
}

func rar5SingleFile(name string, data []byte, hasCRC bool, extra []byte) []byte {
	p := rar5Part{
		first: true, last: true, data: data, unpSize: uint64(len(data)),
		hasCRC: hasCRC, extras: extra,
	}
	var out []byte
	out = append(out, rar5Signature...)
	out = append(out, rar5ArcHeader(false, 0)...)
	out = append(out, rar5FileHeader(name, p, data)...)
	out = append(out, rar5EndHeader(false)...)
	return out
}

func rar5File(name string, data []byte, hasCRC, hasBLAKE bool) []byte {
	var extra []byte
	if hasBLAKE {
		extra = hashExtra(0, blake2Sum(data), nil)
	}
	return rar5SingleFile(name, data, hasCRC, extra)
}

// ---- in memory fs.FS ----

type memFile struct {
	*bytes.Reader
	name string
}

func (f *memFile) Close() error { return nil }
func (f *memFile) Stat() (fs.FileInfo, error) {
	return memFileInfo{name: f.name, size: int64(f.Reader.Size())}, nil
}

type memFileInfo struct {
	name string
	size int64
}

func (i memFileInfo) Name() string       { return i.name }
func (i memFileInfo) Size() int64        { return i.size }
func (i memFileInfo) Mode() fs.FileMode  { return 0444 }
func (i memFileInfo) ModTime() time.Time { return time.Time{} }
func (i memFileInfo) IsDir() bool        { return false }
func (i memFileInfo) Sys() any           { return nil }

type memFS struct {
	files map[string][]byte
}

func (m *memFS) Open(name string) (fs.File, error) {
	data, ok := m.files[name]
	if !ok {
		return nil, &fs.PathError{Op: "open", Path: name, Err: fs.ErrNotExist}
	}
	return &memFile{Reader: bytes.NewReader(data), name: name}, nil
}

// sequentialReader hides Seek so NewReader takes the non seekable path.
type sequentialReader struct{ r io.Reader }

func (s sequentialReader) Read(p []byte) (int, error) { return s.r.Read(p) }

var consumeModes = []string{"read", "read1", "readsmall", "writeto", "copy", "mixed"}

func readAllCurrent(t *testing.T, r interface {
	Read([]byte) (int, error)
	ReadByte() (byte, error)
	WriteTo(io.Writer) (int64, error)
}, mode string) []byte {
	t.Helper()
	var buf bytes.Buffer
	switch mode {
	case "read1":
		for {
			b, err := r.ReadByte()
			if err == io.EOF {
				return buf.Bytes()
			}
			if err != nil {
				t.Fatalf("ReadByte: %v", err)
			}
			buf.WriteByte(b)
		}
	case "readsmall":
		p := make([]byte, 7)
		for {
			n, err := r.Read(p)
			buf.Write(p[:n])
			if err == io.EOF {
				return buf.Bytes()
			}
			if err != nil {
				t.Fatalf("Read(7): %v", err)
			}
		}
	case "writeto":
		if _, err := r.WriteTo(&buf); err != nil {
			t.Fatalf("WriteTo: %v", err)
		}
		return buf.Bytes()
	case "copy":
		if _, err := io.Copy(&buf, r); err != nil {
			t.Fatalf("io.Copy: %v", err)
		}
		return buf.Bytes()
	case "mixed":
		for i := 0; i < 3; i++ {
			b, err := r.ReadByte()
			if err == io.EOF {
				return buf.Bytes()
			}
			if err != nil {
				t.Fatalf("ReadByte: %v", err)
			}
			buf.WriteByte(b)
		}
		p := make([]byte, 10)
		n, _ := io.ReadFull(r, p)
		buf.Write(p[:n])
		if buf.Len() < 3 {
			t.Fatal("mixed mode setup")
		}
		if _, err := r.WriteTo(&buf); err != nil {
			t.Fatalf("WriteTo after Read: %v", err)
		}
		return buf.Bytes()
	default:
		p := make([]byte, 4096)
		for {
			n, err := r.Read(p)
			buf.Write(p[:n])
			if err == io.EOF {
				return buf.Bytes()
			}
			if err != nil {
				t.Fatalf("Read: %v", err)
			}
		}
	}
}

func consumeExpectError(r interface {
	Read([]byte) (int, error)
	ReadByte() (byte, error)
	WriteTo(io.Writer) (int64, error)
}, mode string) error {
	switch mode {
	case "read1":
		for {
			if _, err := r.ReadByte(); err != nil {
				return err
			}
		}
	case "writeto":
		_, err := r.WriteTo(io.Discard)
		return err
	default:
		p := make([]byte, 13)
		for {
			n, err := r.Read(p)
			if err != nil {
				return err
			}
			_ = n
		}
	}
}

// ---- single volume tests ----

func TestBLAKE2spStoredValid(t *testing.T) {
	data := bytes.Repeat([]byte("the quick brown fox "), 50)
	archive := rar5File("a.txt", data, false, true)
	for _, mode := range consumeModes {
		r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
		if err != nil {
			t.Fatal(err)
		}
		hdr, err := r.Next()
		if err != nil {
			t.Fatalf("mode %s Next: %v", mode, err)
		}
		if hdr.Name != "a.txt" || hdr.UnPackedSize != int64(len(data)) {
			t.Fatalf("bad header: %+v", hdr)
		}
		if got := readAllCurrent(t, r, mode); !bytes.Equal(got, data) {
			t.Fatalf("mode %s: content mismatch", mode)
		}
	}
}

func TestBLAKE2spEmptyFile(t *testing.T) {
	archive := rar5File("empty", nil, false, true)
	for _, mode := range consumeModes {
		r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
		if err != nil {
			t.Fatal(err)
		}
		if _, err := r.Next(); err != nil {
			t.Fatal(err)
		}
		if got := readAllCurrent(t, r, mode); len(got) != 0 {
			t.Fatalf("mode %s: expected empty content, got %d bytes", mode, len(got))
		}
	}
}

func TestBLAKE2spAndCRC32BothValid(t *testing.T) {
	data := []byte("both crc32 and blake2sp are declared and verified")
	archive := rar5File("both.txt", data, true, true)
	r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	if _, err := io.Copy(&buf, r); err != nil {
		t.Fatalf("both checksums should pass: %v", err)
	}
	if !bytes.Equal(buf.Bytes(), data) {
		t.Fatal("content mismatch")
	}
}

func TestBLAKE2spBadDigestRejected(t *testing.T) {
	data := bytes.Repeat([]byte("integrity matters"), 20)
	for _, mode := range consumeModes {
		bad := bytes.Clone(blake2Sum(data))
		bad[0] ^= 0xff
		archive := rar5SingleFile("bad.txt", data, false, hashExtra(0, bad, nil))
		r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
		if err != nil {
			t.Fatal(err)
		}
		if _, err := r.Next(); err != nil {
			t.Fatal(err)
		}
		if err := consumeExpectError(r, mode); !errors.Is(err, ErrBadFileChecksum) {
			t.Fatalf("mode %s: expected ErrBadFileChecksum, got %v", mode, err)
		}
	}
}

func TestBLAKE2spCorruptDataRejected(t *testing.T) {
	data := bytes.Repeat([]byte("corrupt me please"), 20)
	archive := rar5File("corrupt.txt", data, false, true)
	// flip a byte inside the packed data area (right before the end block)
	archive[len(archive)-len(rar5EndHeader(false))-len(data)+3] ^= 0xff
	r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); err != nil {
		t.Fatal(err)
	}
	if err := consumeExpectError(r, "copy"); !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("expected ErrBadFileChecksum, got %v", err)
	}
}

func TestCRC32OnlyStillWorks(t *testing.T) {
	data := []byte("legacy rar5 crc32 only archive")
	archive := rar5File("crc.txt", data, true, false)
	r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); err != nil {
		t.Fatal(err)
	}
	var buf bytes.Buffer
	if _, err := io.Copy(&buf, r); err != nil {
		t.Fatalf("crc32 archive failed: %v", err)
	}
	if !bytes.Equal(buf.Bytes(), data) {
		t.Fatal("content mismatch")
	}

	// a corrupted packed byte must still be caught by the CRC32
	bad := rar5File("crc.txt", data, true, false)
	bad[len(bad)-len(rar5EndHeader(false))-len(data)+2] ^= 0x01
	r2, err := NewReader(sequentialReader{bytes.NewReader(bad)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r2.Next(); err != nil {
		t.Fatal(err)
	}
	if err := consumeExpectError(r2, "copy"); !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("crc32 corruption must fail: %v", err)
	}
}

func TestSkipCheckExempts(t *testing.T) {
	data := bytes.Repeat([]byte("skip"), 10)
	bad := bytes.Clone(blake2Sum(data))
	bad[0] ^= 0xff
	archive := rar5SingleFile("s.txt", data, false, hashExtra(0, bad, nil))
	r, err := NewReader(sequentialReader{bytes.NewReader(archive)}, SkipCheck)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); err != nil {
		t.Fatal(err)
	}
	if _, err := io.Copy(io.Discard, r); err != nil {
		t.Fatalf("SkipCheck should exempt checksum verification: %v", err)
	}
}

func TestCloseUnreadDoesNotVerify(t *testing.T) {
	data := bytes.Repeat([]byte("x"), 100)
	bad := bytes.Clone(blake2Sum(data))
	bad[0] ^= 0xff
	archive := rar5SingleFile("u.txt", data, false, hashExtra(0, bad, nil))
	fsys := &memFS{files: map[string][]byte{"u.part01.rar": archive}}
	files, err := List("u.part01.rar", FileSystem(fsys))
	if err != nil {
		t.Fatal(err)
	}
	f, err := files[0].Open()
	if err != nil {
		t.Fatal(err)
	}
	if err := f.Close(); err != nil {
		t.Fatalf("closing unread file: %v", err)
	}
}

func TestIncompleteHashRecordRejected(t *testing.T) {
	data := []byte("hi")
	// record type 2, hash type 0 with only 10 of the required 32 bytes
	raw := append([]byte{0}, make([]byte, 10)...)
	archive := rar5SingleFile("inc.txt", data, false, hashExtra(0, nil, raw))
	r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); !errors.Is(err, ErrCorruptFileHeader) {
		t.Fatalf("sequential read: expected ErrCorruptFileHeader, got %v", err)
	}
	fsys := &memFS{files: map[string][]byte{"i.part01.rar": archive}}
	if _, err := List("i.part01.rar", FileSystem(fsys)); err == nil {
		t.Fatal("List: incomplete hash record must produce an error")
	}
}

func TestUnknownHashTypeIgnored(t *testing.T) {
	data := []byte("forward compatibility")
	raw := append(encVint(7), make([]byte, 40)...)
	archive := rar5SingleFile("unk.txt", data, true, hashExtra(0, nil, raw))
	r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); err != nil {
		t.Fatalf("unknown optional hash type must be ignored: %v", err)
	}
	var buf bytes.Buffer
	if _, err := io.Copy(&buf, r); err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(buf.Bytes(), data) {
		t.Fatal("content mismatch")
	}
}

// ---- compressed archive, built from a hand crafted RAR5 literal stream ----

// bitWriter packs values MSB first into bytes, matching the RAR5 bit
// reader: the first emitted bit lands at bit 7 of the current byte.
type bitWriter struct {
	buf   []byte
	cur   byte
	n     uint8
	count int
}

func (w *bitWriter) bits(v int, n uint8) {
	for i := int(n) - 1; i >= 0; i-- {
		w.cur |= byte((v>>uint(i))&1) << (7 - w.n)
		w.n++
		w.count++
		if w.n == 8 {
			w.buf = append(w.buf, w.cur)
			w.cur, w.n = 0, 0
		}
	}
}

func (w *bitWriter) bytes() ([]byte, int) {
	if w.n > 0 {
		return append(append([]byte{}, w.buf...), w.cur), w.count
	}
	return w.buf, w.count
}

// rar5LiteralStream builds a valid RAR5 compressed stream that expands to
// copies of the given (single distinct) byte repeated unpSize times.
// It uses one last block with a fresh Huffman table: main alphabet symbol
// for the literal has code length 1, every other symbol length 0.
func rar5LiteralStream(value byte, unpSize int) []byte {
	var w bitWriter

	// 20 code length table nibbles. Pre-Huffman lengths of 2 for sym0,
	// sym1 and sym19 give canonical codes 00, 01 and 10 (11 unused).
	w.bits(2, 4) // symbol 0 code length
	w.bits(2, 4) // symbol 1 code length
	for i := 2; i < 20; i++ {
		nib := 0
		if i == 19 {
			nib = 2 // symbol 19 gets code length 2
		}
		w.bits(nib, 4)
	}

	// Main code length table (306 entries).
	// symbol 19 = run of zeros, count encoded in 7 bits + 11 (max 138).
	zeroRun := func(n int) {
		w.bits(0b10, 2) // symbol 19, canonical code 10
		w.bits(n-11, 7)
	}
	zeros := func(n int) {
		for n > 0 {
			c := min(n, 138)
			zeroRun(c)
			n -= c
		}
	}
	zeros(int(value)) // symbols before the literal
	w.bits(0b01, 2)   // symbol 1: canonical code 01, code length 1 follows
	zeros(mainSize5 - int(value) - 1)

	// Offset, low offset and length tables contain only zero lengths.
	zeros(offsetSize5)
	zeros(lowoffsetSize5)
	zeros(lengthSize5)

	// Compressed data: unpSize copies of the 1 bit literal code.
	for i := 0; i < unpSize; i++ {
		w.bits(0, 1)
	}

	stream, bits := w.bytes()

	// The block bit limit is (flags&7)+1 + (blockBytes-1)*8 and must equal
	// the exact number of meaningful stream bits.
	base := (bits-1)%8 + 1
	blockBytes := (bits-base)/8 + 1
	if blockBytes > 0xffffff {
		panic("block too large")
	}
	flags := byte(0x40 | 0x80 | (base - 1)) // last block, new huffman table
	hsum := byte(0x5a) ^ flags ^ byte(blockBytes)
	header := []byte{flags, hsum, byte(blockBytes)}
	return append(header, stream...)
}

func buildCompressedArchive(t *testing.T, addHash, tamperPacked bool, digestOverride []byte) ([]byte, []byte) {
	t.Helper()
	unp := bytes.Repeat([]byte{'A'}, 36)
	packed := rar5LiteralStream('A', len(unp))
	if tamperPacked {
		packed[len(packed)-1] ^= 0xff
	}

	var extra []byte
	if addHash {
		digest := blake2Sum(unp)
		if digestOverride != nil {
			digest = digestOverride
		}
		extra = hashExtra(0, digest, nil)
	}

	p := rar5Part{
		first: true, last: true, data: packed, unpSize: uint64(len(unp)),
		hasCRC: true, compInfo: 0x80, extras: extra, // method 1, ver 0
	}
	var out []byte
	out = append(out, rar5Signature...)
	out = append(out, rar5ArcHeader(false, 0)...)
	out = append(out, rar5FileHeader("a.txt", p, unp)...)
	out = append(out, rar5EndHeader(false)...)
	return out, unp
}

func TestCompressedBLAKE2sp(t *testing.T) {
	archive, unp := buildCompressedArchive(t, true, false, nil)
	for _, mode := range consumeModes {
		r, err := NewReader(sequentialReader{bytes.NewReader(archive)})
		if err != nil {
			t.Fatal(err)
		}
		if _, err := r.Next(); err != nil {
			t.Fatal(err)
		}
		if got := readAllCurrent(t, r, mode); !bytes.Equal(got, unp) {
			t.Fatalf("mode %s: compressed content mismatch (%d bytes)", mode, len(got))
		}
	}

	// wrong BLAKE2 digest with valid compressed data
	bad := bytes.Clone(blake2Sum(unp))
	bad[1] ^= 0x10
	badArchive, _ := buildCompressedArchive(t, true, false, bad)
	r, err := NewReader(sequentialReader{bytes.NewReader(badArchive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r.Next(); err != nil {
		t.Fatal(err)
	}
	if err := consumeExpectError(r, "copy"); !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("compressed bad blake2: expected ErrBadFileChecksum, got %v", err)
	}

	// corrupted packed stream must surface an error, never silent success
	corruptArchive, _ := buildCompressedArchive(t, true, true, nil)
	r2, err := NewReader(sequentialReader{bytes.NewReader(corruptArchive)})
	if err != nil {
		t.Fatal(err)
	}
	if _, err := r2.Next(); err != nil {
		t.Fatal(err)
	}
	if err := consumeExpectError(r2, "copy"); err == nil {
		t.Fatal("corrupt compressed data must not decode successfully")
	}
}

// ---- multi volume ----

type splitOpts struct {
	hasCRC, hasBLAKE bool
	password         string
	useMac           bool
	kdfCount         byte
	crcD1, blakeD1   []byte // declared digests overrides for part 1
	crcD2, blakeD2   []byte // declared digests overrides for part 2
	tamper1, tamper2 *int   // packed data index to flip
}

func buildSplitStored(t *testing.T, data []byte, splitAt int, o splitOpts) *memFS {
	t.Helper()
	salt := bytes.Repeat([]byte{0x41}, 16)
	iv := bytes.Repeat([]byte{0x77}, 16)

	var keyData []byte
	var packed1, packed2 []byte
	var cryptRec []byte
	if o.password != "" {
		if splitAt%16 != 0 || len(data)%16 != 0 {
			t.Fatal("encrypted split tests need 16 byte aligned sizes")
		}
		keys := calcKeys50([]byte(o.password), salt, 1<<o.kdfCount)
		block, err := aes.NewCipher(keys[0])
		if err != nil {
			t.Fatal(err)
		}
		cipherAll := make([]byte, len(data))
		cipher.NewCBCEncrypter(block, iv).CryptBlocks(cipherAll, data)
		packed1, packed2 = cipherAll[:splitAt], cipherAll[splitAt:]
		if o.useMac {
			keyData = keys[1]
		}
		cryptRec = cryptExtra(o.kdfCount, salt, iv, nil, o.useMac)
	} else {
		packed1, packed2 = data[:splitAt], data[splitAt:]
	}

	// partExtras assembles the encryption and file hash records for a part.
	// Non-last parts declare hashes over their packed data, the last part
	// declares hashes over the whole unpacked file.
	partExtras := func(last bool, packed, blakeOverride []byte) []byte {
		var ex []byte
		if cryptRec != nil {
			ex = append(ex, cryptRec...)
		}
		if o.hasBLAKE {
			digest := blakeOverride
			if digest == nil {
				if last {
					digest = blake2Sum(data)
				} else {
					digest = blake2Sum(packed)
				}
				if keyData != nil {
					digest = macDigest(keyData, digest)
				}
			}
			ex = append(ex, hashExtra(0, digest, nil)...)
		}
		return ex
	}

	p1 := rar5Part{
		first: true, data: packed1, unpSize: uint64(len(data)),
		hasCRC: o.hasCRC, crcDigest: o.crcD1,
		extras: partExtras(false, packed1, o.blakeD1),
	}
	p2 := rar5Part{
		last: true, data: packed2, unpSize: uint64(len(data)),
		hasCRC: o.hasCRC, crcDigest: o.crcD2,
		extras: partExtras(true, packed2, o.blakeD2),
	}

	head1 := rar5FileHeader("split.bin", p1, data)
	head2 := rar5FileHeader("split.bin", p2, data)
	if o.tamper1 != nil {
		head1[len(head1)-splitAt+*o.tamper1] ^= 0xff
	}
	if o.tamper2 != nil {
		head2[len(head2)-(len(data)-splitAt)+*o.tamper2] ^= 0xff
	}

	vol1 := append(rar5Signature, rar5ArcHeader(true, 0)...)
	vol1 = append(vol1, head1...)
	vol1 = append(vol1, rar5EndHeader(true)...)
	vol2 := append(rar5Signature, rar5ArcHeader(true, 2)...)
	vol2 = append(vol2, head2...)
	vol2 = append(vol2, rar5EndHeader(false)...)

	return &memFS{files: map[string][]byte{
		"s.part01.rar": vol1,
		"s.part02.rar": vol2,
	}}
}

func openSplit(t *testing.T, fsys *memFS, opts ...Option) *ReadCloser {
	t.Helper()
	rc, err := OpenReader("s.part01.rar", append([]Option{FileSystem(fsys)}, opts...)...)
	if err != nil {
		t.Fatal(err)
	}
	if _, err := rc.Next(); err != nil {
		t.Fatal(err)
	}
	return rc
}

func TestSplitVolumesValid(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30) // 660 bytes
	fsys := buildSplitStored(t, data, 200, splitOpts{hasCRC: true, hasBLAKE: true})
	for _, mode := range consumeModes {
		rc := openSplit(t, fsys)
		var buf bytes.Buffer
		err := copyReadCloser(rc, &buf, mode)
		rc.Close()
		if err != nil {
			t.Fatalf("mode %s: %v", mode, err)
		}
		if !bytes.Equal(buf.Bytes(), data) {
			t.Fatalf("mode %s: content mismatch", mode)
		}
	}
}

func TestSplitVolumesPackedDigestBad(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30)
	badPacked := bytes.Repeat([]byte{0x11}, 32)
	fsys := buildSplitStored(t, data, 200, splitOpts{hasBLAKE: true, blakeD1: badPacked})
	rc := openSplit(t, fsys)
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("non-last part packed digest mismatch must fail: %v", err)
	}
}

func TestSplitVolumesPackedDataBad(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30)
	idx := 5
	fsys := buildSplitStored(t, data, 200, splitOpts{hasCRC: true, hasBLAKE: true, tamper1: &idx})
	rc := openSplit(t, fsys)
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("tampered packed data in non-last part must fail at boundary: %v", err)
	}
}

func TestSplitVolumesLastDataBad(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30)
	idx := 7
	fsys := buildSplitStored(t, data, 200, splitOpts{hasCRC: true, hasBLAKE: true, tamper2: &idx})
	rc := openSplit(t, fsys)
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("tampered data in last part must fail whole-file check: %v", err)
	}
}

func TestSplitVolumesUnpackedDigestBad(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30)
	bad := bytes.Repeat([]byte{0x22}, 32)
	fsys := buildSplitStored(t, data, 200, splitOpts{hasBLAKE: true, blakeD2: bad})
	rc := openSplit(t, fsys)
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("whole file unpacked digest mismatch must fail: %v", err)
	}
}

func TestSplitVolumesSkipCheck(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30)
	bad := bytes.Repeat([]byte{0x22}, 32)
	fsys := buildSplitStored(t, data, 200, splitOpts{hasBLAKE: true, blakeD2: bad})
	rc := openSplit(t, fsys, SkipCheck)
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if err != nil {
		t.Fatalf("SkipCheck must exempt split verification: %v", err)
	}
}

func TestSplitVolumesCRCPackedScope(t *testing.T) {
	// CRC32 only: non-last part carries packed CRC, last carries whole
	// file CRC, and both scopes are enforced.
	data := bytes.Repeat([]byte("crc-split-scope!!"), 40) // 640
	fsys := buildSplitStored(t, data, 240, splitOpts{hasCRC: true})
	rc := openSplit(t, fsys)
	var buf bytes.Buffer
	if _, err := io.Copy(&buf, rc); err != nil {
		t.Fatalf("valid crc split: %v", err)
	}
	rc.Close()
	if !bytes.Equal(buf.Bytes(), data) {
		t.Fatal("content mismatch")
	}

	// bad packed CRC in the non-last part
	bad1 := bytes.Repeat([]byte{0xee}, 4)
	fsysBad := buildSplitStored(t, data, 240, splitOpts{hasCRC: true, crcD1: bad1})
	rc = openSplit(t, fsysBad)
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("non-last packed CRC32 must be enforced: %v", err)
	}

	// bad whole-file CRC in the last part
	bad2 := bytes.Repeat([]byte{0xee}, 4)
	fsysBad = buildSplitStored(t, data, 240, splitOpts{hasCRC: true, crcD2: bad2})
	rc = openSplit(t, fsysBad)
	_, err = io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("whole file CRC32 must be enforced: %v", err)
	}
}

// ---- encryption with checksum transformation ----

func TestEncryptedBLAKE2spMAC(t *testing.T) {
	password := "correct horse battery staple"
	kdfCount := byte(4)
	salt := bytes.Repeat([]byte{0x5a}, 16)
	iv := bytes.Repeat([]byte{0x3c}, 16)

	for _, useMac := range []bool{true, false} {
		data := []byte("secret-encrypted-file-data!!!!!!") // 32 bytes
		if len(data) != 32 {
			t.Fatalf("test data length %d not block aligned", len(data))
		}
		keys := calcKeys50([]byte(password), salt, 1<<kdfCount)
		block, err := aes.NewCipher(keys[0])
		if err != nil {
			t.Fatal(err)
		}
		cipherBytes := make([]byte, len(data))
		cipher.NewCBCEncrypter(block, iv).CryptBlocks(cipherBytes, data)

		var digest []byte
		if useMac {
			digest = macDigest(keys[1], blake2Sum(data))
		} else {
			digest = blake2Sum(data)
		}
		extra := cryptExtra(kdfCount, salt, iv, nil, useMac)
		extra = append(extra, hashExtra(0, digest, nil)...)
		archive := rar5SingleFile("secret.bin", cipherBytes, false, extra)

		// correct password: data decrypts and verifies, independent of how
		// it is consumed
		for _, mode := range consumeModes {
			r, err := NewReader(sequentialReader{bytes.NewReader(archive)}, Password(password))
			if err != nil {
				t.Fatal(err)
			}
			if _, err := r.Next(); err != nil {
				t.Fatalf("useMac=%v Next: %v", useMac, err)
			}
			if got := readAllCurrent(t, r, mode); !bytes.Equal(got, data) {
				t.Fatalf("useMac=%v mode %s decrypted content mismatch", useMac, mode)
			}
		}

		// wrong declared digest is still rejected
		bad := bytes.Clone(digest)
		bad[0] ^= 0x55
		badExtra := cryptExtra(kdfCount, salt, iv, nil, useMac)
		badExtra = append(badExtra, hashExtra(0, bad, nil)...)
		badArchive := rar5SingleFile("secret.bin", cipherBytes, false, badExtra)
		r2, err := NewReader(sequentialReader{bytes.NewReader(badArchive)}, Password(password))
		if err != nil {
			t.Fatal(err)
		}
		if _, err := r2.Next(); err != nil {
			t.Fatal(err)
		}
		if _, err := io.Copy(io.Discard, r2); !errors.Is(err, ErrBadFileChecksum) {
			t.Fatalf("useMac=%v wrong digest must fail: %v", useMac, err)
		}

		// wrong password: file body must not be readable
		r3, err := NewReader(sequentialReader{bytes.NewReader(archive)}, Password("wrong"))
		if err != nil {
			t.Fatal(err)
		}
		if _, err := r3.Next(); err != nil {
			t.Fatal(err)
		}
		if _, err := io.Copy(io.Discard, r3); err == nil {
			t.Fatalf("useMac=%v wrong password must not verify", useMac)
		}
	}
}

func TestEncryptedSplitBLAKE2spMAC(t *testing.T) {
	password := "pw"
	data := bytes.Repeat([]byte("encrypted-split-file-content-"), 16) // 512 bytes
	fsys := buildSplitStored(t, data, 208, splitOpts{
		hasBLAKE: true, password: password, useMac: true, kdfCount: 4,
	})
	rc := openSplit(t, fsys, Password(password))
	var buf bytes.Buffer
	if _, err := io.Copy(&buf, rc); err != nil {
		t.Fatalf("encrypted split valid data should pass: %v", err)
	}
	rc.Close()
	if !bytes.Equal(buf.Bytes(), data) {
		t.Fatal("encrypted split content mismatch")
	}

	// wrong whole-file digest in the last part
	bad := bytes.Repeat([]byte{0x33}, 32)
	fsysBad := buildSplitStored(t, data, 208, splitOpts{
		hasBLAKE: true, password: password, useMac: true, kdfCount: 4, blakeD2: bad,
	})
	rc = openSplit(t, fsysBad, Password(password))
	_, err := io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("encrypted split bad digest must fail: %v", err)
	}

	// tampered ciphertext in the first part fails the packed MAC check
	encIdx := 3
	fsysBad = buildSplitStored(t, data, 208, splitOpts{
		hasBLAKE: true, password: password, useMac: true, kdfCount: 4, tamper1: &encIdx,
	})
	rc = openSplit(t, fsysBad, Password(password))
	_, err = io.Copy(io.Discard, rc)
	rc.Close()
	if !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("encrypted split tampered first part must fail packed check: %v", err)
	}
}

// ---- OpenFS / List / OpenFSCheck policies ----

func TestOpenFSPolicies(t *testing.T) {
	data := bytes.Repeat([]byte("fs policy data"), 10)
	good := rar5File("dir/file.txt", data, false, true)
	badDigest := bytes.Clone(blake2Sum(data))
	badDigest[0] ^= 0xff
	bad := rar5SingleFile("dir/file.txt", data, false, hashExtra(0, badDigest, nil))
	fsysBad := &memFS{files: map[string][]byte{"p.part01.rar": bad}}

	// default List must not verify contents
	files, err := List("p.part01.rar", FileSystem(fsysBad))
	if err != nil {
		t.Fatalf("List must not verify contents: %v", err)
	}
	if len(files) != 1 || files[0].Name != "dir/file.txt" {
		t.Fatalf("unexpected list: %+v", files)
	}
	// but fully reading the listed file must verify and fail
	f, err := files[0].Open()
	if err != nil {
		t.Fatal(err)
	}
	if _, err := io.Copy(io.Discard, f); !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("full read after List must verify: %v", err)
	}
	f.Close()

	// default OpenFS builds without verification, ReadFile verifies
	rfs, err := OpenFS("p.part01.rar", FileSystem(fsysBad))
	if err != nil {
		t.Fatalf("OpenFS must not verify while building: %v", err)
	}
	if _, err := rfs.ReadFile("dir/file.txt"); !errors.Is(err, ErrBadFileChecksum) {
		t.Fatalf("ReadFile must verify: %v", err)
	}
	rfsSkip, err := OpenFS("p.part01.rar", FileSystem(fsysBad), SkipCheck)
	if err != nil {
		t.Fatal(err)
	}
	if b, err := rfsSkip.ReadFile("dir/file.txt"); err != nil || !bytes.Equal(b, data) {
		t.Fatalf("SkipCheck must exempt ReadFile: %v %d", err, len(b))
	}

	// OpenFSCheck verifies while building and fails on corruption
	if _, err := OpenFS("p.part01.rar", FileSystem(fsysBad), OpenFSCheck); err == nil {
		t.Fatal("OpenFSCheck must reject corrupt content while building")
	}
	// OpenFSCheck takes precedence over SkipCheck
	if _, err := OpenFS("p.part01.rar", FileSystem(fsysBad), OpenFSCheck, SkipCheck); err == nil {
		t.Fatal("OpenFSCheck must take precedence over SkipCheck")
	}
	// valid archive passes OpenFSCheck and remains readable
	fsysGood := &memFS{files: map[string][]byte{"p.part01.rar": good}}
	rfs2, err := OpenFS("p.part01.rar", FileSystem(fsysGood), OpenFSCheck)
	if err != nil {
		t.Fatalf("valid archive must pass OpenFSCheck: %v", err)
	}
	if b, err := rfs2.ReadFile("dir/file.txt"); err != nil || !bytes.Equal(b, data) {
		t.Fatalf("verified file read failed: %v", err)
	}
}

func TestSplitVolumesOpenFSCheck(t *testing.T) {
	data := bytes.Repeat([]byte("volume boundary data-"), 30)
	fsys := buildSplitStored(t, data, 200, splitOpts{hasBLAKE: true})
	if _, err := OpenFS("s.part01.rar", FileSystem(fsys), OpenFSCheck); err != nil {
		t.Fatalf("valid split set must pass OpenFSCheck: %v", err)
	}

	// corrupt packed digest in the non-last volume fails while building
	badPacked := bytes.Repeat([]byte{0x44}, 32)
	fsysBad := buildSplitStored(t, data, 200, splitOpts{hasBLAKE: true, blakeD1: badPacked})
	if _, err := OpenFS("s.part01.rar", FileSystem(fsysBad), OpenFSCheck); err == nil {
		t.Fatal("OpenFSCheck must reject non-last part digest mismatch")
	}
	// and OpenFSCheck still wins over SkipCheck
	if _, err := OpenFS("s.part01.rar", FileSystem(fsysBad), OpenFSCheck, SkipCheck); err == nil {
		t.Fatal("OpenFSCheck must take precedence over SkipCheck for volumes too")
	}
}

func TestFileOpenVerifies(t *testing.T) {
	data := bytes.Repeat([]byte("open-me"), 8)
	archive := rar5File("o.txt", data, false, true)
	fsys := &memFS{files: map[string][]byte{"o.part01.rar": archive}}
	files, err := List("o.part01.rar", FileSystem(fsys))
	if err != nil {
		t.Fatal(err)
	}
	f, err := files[0].Open()
	if err != nil {
		t.Fatal(err)
	}
	b, err := io.ReadAll(f)
	if err != nil || !bytes.Equal(b, data) {
		t.Fatalf("File.Open full read: %v %d", err, len(b))
	}
	f.Close()
}

func copyReadCloser(rc *ReadCloser, w io.Writer, mode string) error {
	switch mode {
	case "read1":
		for {
			b, err := rc.ReadByte()
			if err == io.EOF {
				return nil
			}
			if err != nil {
				return err
			}
			_, _ = w.Write([]byte{b})
		}
	case "writeto":
		_, err := rc.WriteTo(w)
		if errors.Is(err, io.EOF) {
			return nil
		}
		return err
	case "mixed":
		for i := 0; i < 5; i++ {
			b, err := rc.ReadByte()
			if err == io.EOF {
				return nil
			}
			if err != nil {
				return err
			}
			_, _ = w.Write([]byte{b})
		}
		p := make([]byte, 40)
		n, err := rc.Read(p)
		_, _ = w.Write(p[:n])
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return err
		}
		_, err = rc.WriteTo(w)
		if errors.Is(err, io.EOF) {
			return nil
		}
		return err
	default:
		_, err := io.Copy(w, rc)
		return err
	}
}
