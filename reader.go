package rardecode

import (
	"bytes"
	"crypto/hmac"
	"crypto/sha256"
	"errors"
	"hash"
	"io"
	"io/fs"
	"math"
	"sync"
	"time"
)

// FileHeader HostOS types
const (
	HostOSUnknown = 0
	HostOSMSDOS   = 1
	HostOSOS2     = 2
	HostOSWindows = 3
	HostOSUnix    = 4
	HostOSMacOS   = 5
	HostOSBeOS    = 6

	LinkTypeNone            = 0
	LinkTypeUnixSymlink     = 1
	LinkTypeWindowsSymlink  = 2
	LinkTypeWindowsJunction = 3
	LinkTypeHardLink        = 4
	LinkTypeFileCopy        = 5
)

const (
	maxPassword = int(128)
)

var (
	ErrShortFile        = errors.New("rardecode: decoded file too short")
	ErrInvalidFileBlock = errors.New("rardecode: invalid file block")
	ErrUnexpectedArcEnd = errors.New("rardecode: unexpected end of archive")
	ErrBadFileChecksum  = errors.New("rardecode: bad file checksum")
	ErrSolidOpen        = errors.New("rardecode: solid files don't support Open")
	ErrUnknownVersion   = errors.New("rardecode: unknown archive version")
)

// FileHeader represents a single file in a RAR archive.
type FileHeader struct {
	Name               string    // file name using '/' as the directory separator
	IsDir              bool      // is a directory
	Solid              bool      // is a solid file
	Encrypted          bool      // file contents are encrypted
	HeaderEncrypted    bool      // file header is encrypted
	HostOS             byte      // Host OS the archive was created on
	Attributes         int64     // Host OS specific file attributes
	PackedSize         int64     // packed file size (or first block if the file spans volumes)
	UnPackedSize       int64     // unpacked file size
	UnKnownSize        bool      // unpacked file size is not known
	ModificationTime   time.Time // modification time (non-zero if set)
	CreationTime       time.Time // creation time (non-zero if set)
	AccessTime         time.Time // access time (non-zero if set)
	Version            int       // file version
	LinkType           byte      // the type of redirection link for the file
	LinkTarget         string    // target path of the LinkType
	LinkTargetIsDir    bool      // link target is a directory
	UnixOwnerUserName  *string   // unix owner user name
	UnixOwnerGroupName *string   // unix owner group name
	UnixOwnerUserID    *uint64   // unix owner user id
	UnixOwnerGroupID   *uint64   // unix owner group id
}

// Mode returns an fs.FileMode for the file, calculated from the Attributes field.
func (f *FileHeader) Mode() fs.FileMode {
	var m fs.FileMode

	if f.IsDir {
		m = fs.ModeDir
	}
	if f.HostOS == HostOSWindows {
		if f.IsDir {
			m |= 0777
		} else if f.Attributes&1 > 0 {
			m |= 0444 // readonly
		} else {
			m |= 0666
		}
		return m
	}
	// assume unix perms for all remaining os types
	m |= fs.FileMode(f.Attributes) & fs.ModePerm

	// only check other bits on unix host created archives
	if f.HostOS != HostOSUnix {
		return m
	}

	if f.Attributes&0x200 != 0 {
		m |= fs.ModeSticky
	}
	if f.Attributes&0x400 != 0 {
		m |= fs.ModeSetgid
	}
	if f.Attributes&0x800 != 0 {
		m |= fs.ModeSetuid
	}

	// Check for additional file types.
	if f.Attributes&0xF000 == 0xA000 || f.LinkType == LinkTypeWindowsSymlink || f.LinkType == LinkTypeUnixSymlink {
		m |= fs.ModeSymlink
	}
	return m
}

type byteReader interface {
	io.Reader
	io.ByteReader
}

type archiveFile interface {
	byteReader
	io.WriterTo
	writeToN(w io.Writer, n int64) (int64, error)
	currFile() *fileBlockHeader
	nextFile() (*fileBlockList, error)
	newArchiveFile(blocks *fileBlockList) (archiveFile, error)
	Stat() (fs.FileInfo, error)
}

type archiveFileSeeker interface {
	archiveFile
	io.Seeker
}

type fileCloser struct {
	archiveFile
	io.Closer
}

type fileSeekCloser struct {
	archiveFileSeeker
	io.Closer
}

type errorFile struct {
	archiveFile
	err error
}

func (ef *errorFile) ReadByte() (byte, error)                      { return 0, ef.err }
func (ef *errorFile) Read(p []byte) (int, error)                   { return 0, ef.err }
func (ef *errorFile) WriteTo(w io.Writer) (int64, error)           { return 0, ef.err }
func (ef *errorFile) writeToN(w io.Writer, n int64) (int64, error) { return 0, ef.err }

type fileBlockList struct {
	mu     sync.RWMutex
	blocks []*fileBlockHeader
}

func (fl *fileBlockList) firstBlock() *fileBlockHeader {
	fl.mu.RLock()
	defer fl.mu.RUnlock()
	return fl.blocks[0]
}

func (fl *fileBlockList) lastBlock() *fileBlockHeader {
	fl.mu.RLock()
	defer fl.mu.RUnlock()
	return fl.blocks[len(fl.blocks)-1]
}

func (fl *fileBlockList) findBlock(offset int64) *fileBlockHeader {
	fl.mu.RLock()
	defer fl.mu.RUnlock()
	for _, h := range fl.blocks {
		if offset < h.PackedSize || (offset == h.PackedSize && h.last) {
			return h
		}
		offset -= h.PackedSize
	}
	return nil
}

func (fl *fileBlockList) addBlock(h *fileBlockHeader) {
	fl.mu.Lock()
	defer fl.mu.Unlock()
	if len(fl.blocks) == h.blocknum {
		fl.blocks = append(fl.blocks, h)
	}
}

func (fl *fileBlockList) isDir() bool {
	fl.mu.RLock()
	defer fl.mu.RUnlock()
	return fl.blocks[0].IsDir
}

func (fl *fileBlockList) hasFileHash() bool {
	fl.mu.RLock()
	defer fl.mu.RUnlock()
	h := fl.blocks[0]
	return h.hash != nil || h.blake2 != nil
}

func (fl *fileBlockList) removeFileHash() {
	fl.mu.Lock()
	defer fl.mu.Unlock()
	h := *fl.blocks[0]
	h.hash = nil
	h.blake2 = nil
	fl.blocks[0] = &h
}

func newFileBlockList(blocks ...*fileBlockHeader) *fileBlockList {
	return &fileBlockList{blocks: blocks}
}

// packedFileReader provides sequential access to packed files in a RAR archive.
type packedFileReader struct {
	v      volume
	h      *fileBlockHeader // current file header
	dr     *decodeReader
	offset int64
	blocks *fileBlockList
	opt    *options

	// Per-volume packed data checksums (RAR 5.0 only). They verify the raw
	// packed bytes of a non-last file part contained in the current volume.
	// The whole unpacked file is verified separately by checksumReader.
	pcOn    bool      // packed data checksums apply to the current block
	pcRead  int64     // packed bytes hashed for the current block
	pcCRC   hash.Hash // packed CRC32 of the current block, nil if not declared
	pcBLAKE hash.Hash // packed BLAKE2sp of the current block, nil if not declared
}

func (f *packedFileReader) init(blocks *fileBlockList) error {
	h := blocks.firstBlock()
	f.h = h
	f.blocks = blocks
	f.offset = 0
	f.resetPackedChecks()
	return nil
}

// resetPackedChecks prepares the packed data checksums for the current file
// block. Non-last blocks of RAR 5.0 files carry checksums of the packed data
// stored in the current volume, last and unsplit blocks carry no packed
// checksum here as their checksum covers the whole unpacked data.
func (f *packedFileReader) resetPackedChecks() {
	f.pcOn = false
	f.pcRead = 0
	f.pcCRC = nil
	f.pcBLAKE = nil

	if f.opt.skipCheck || f.h == nil || f.h.last {
		return
	}
	first := f.blocks.firstBlock()
	if !first.is50 || (first.hash == nil && first.blake2 == nil) {
		return
	}
	f.pcOn = true
	if first.hash != nil && f.h.sum != nil {
		f.pcCRC = newLittleEndianCRC32()
	}
	if first.blake2 != nil && f.h.blake2sum != nil {
		f.pcBLAKE = newBlake2sp()
	}
}

func (f *packedFileReader) feedPackedChecks(p []byte) {
	if !f.pcOn || len(p) == 0 {
		return
	}
	if f.pcCRC != nil {
		_, _ = f.pcCRC.Write(p)
	}
	if f.pcBLAKE != nil {
		_, _ = f.pcBLAKE.Write(p)
	}
	f.pcRead += int64(len(p))
}

// finishPackedBlock verifies the packed data checksums for a fully consumed
// non-last file block. A mismatch is reported as a file checksum error.
func (f *packedFileReader) finishPackedBlock() error {
	if !f.pcOn || f.h == nil || f.h.last || f.pcRead != f.h.PackedSize {
		return nil
	}
	key := f.h.hashKey
	if f.pcCRC != nil {
		sum := f.pcCRC.Sum(nil)
		if len(key) > 0 {
			sum = convertHashToMAC(sum, key)
		}
		if !bytes.Equal(sum, f.h.sum) {
			return ErrBadFileChecksum
		}
	}
	if f.pcBLAKE != nil {
		sum := f.pcBLAKE.Sum(nil)
		if len(key) > 0 {
			sum = convertHashToMAC(sum, key)
		}
		if !bytes.Equal(sum, f.h.blake2sum) {
			return ErrBadFileChecksum
		}
	}
	return nil
}

// packedTapWriter wraps w so every byte written also feeds the packed data
// checksums. It returns w unchanged when no packed checksum is active.
func (f *packedFileReader) packedTapWriter(w io.Writer) io.Writer {
	if !f.pcOn || (f.pcCRC == nil && f.pcBLAKE == nil) {
		return w
	}
	return io.MultiWriter(w, packedFeedWriter{f: f})
}

// packedFeedWriter feeds the packed data checksums. Hash writes never fail,
// so Write always reports the full slice as written.
type packedFeedWriter struct {
	f *packedFileReader
}

func (w packedFeedWriter) Write(p []byte) (int, error) {
	w.f.feedPackedChecks(p)
	return len(p), nil
}

func (f *packedFileReader) Stat() (fs.FileInfo, error) {
	if f.h == nil {
		return nil, fs.ErrInvalid
	}
	return fileInfo{h: f.h}, nil
}

// nextBlock reads the next file block in the current file at the current
// archive file position, or returns an error if there is a problem.
// It is invalid to call this when already at the last block in the current file.
func (f *packedFileReader) nextBlock() error {
	if f.h == nil {
		return io.EOF
	}
	if f.h.last {
		return io.EOF
	}
	h, err := f.v.nextBlock()
	if err != nil {
		switch err {
		case io.EOF:
			// archive ended, but file hasn't
			return ErrUnexpectedArcEnd
		case errVolumeOrArchiveEnd:
			return ErrMultiVolume
		default:
			return err
		}
	}
	if h.first || h.Name != f.h.Name {
		return ErrInvalidFileBlock
	}
	h.packedOff = f.h.packedOff + f.h.PackedSize
	h.blocknum = f.h.blocknum + 1
	f.h = h
	f.offset = h.dataOff
	f.blocks.addBlock(h)
	f.resetPackedChecks()
	return nil
}

// next advances to the next packed file in the RAR archive.
func (f *packedFileReader) nextFile() (*fileBlockList, error) {
	// skip to last block in current file
	var err error
	for err == nil {
		err = f.nextBlock()
	}
	if err != io.EOF {
		return nil, err
	}
	h, err := f.v.nextBlock() // get next file block
	if err != nil {
		if err == errVolumeOrArchiveEnd {
			err = io.EOF
		}
		return nil, err
	}
	if !h.first {
		return nil, ErrInvalidFileBlock
	}
	blocks := newFileBlockList(h)
	err = f.init(blocks)
	if err != nil {
		return nil, err
	}
	return blocks, nil
}

func (f *packedFileReader) currFile() *fileBlockHeader { return f.h }

// Read reads the packed data for the current file into p.
func (f *packedFileReader) Read(p []byte) (int, error) {
	for {
		n, err := f.v.Read(p)
		if n > 0 {
			f.offset += int64(n)
			f.feedPackedChecks(p[:n])
		}
		if err == io.EOF {
			if cerr := f.finishPackedBlock(); cerr != nil {
				return n, cerr
			}
			err = f.nextBlock()
		}
		if n > 0 || err != nil {
			return n, err
		}
	}
}

func (f *packedFileReader) ReadByte() (byte, error) {
	for {
		b, err := f.v.ReadByte()
		if err == nil {
			f.offset++
			f.feedPackedChecks([]byte{b})
			return b, nil
		}
		if err == io.EOF {
			if cerr := f.finishPackedBlock(); cerr != nil {
				return 0, cerr
			}
			err = f.nextBlock()
			if err == nil {
				continue
			}
		}
		return b, err
	}
}

func (f *packedFileReader) writeToN(w io.Writer, n int64) (int64, error) {
	if n == 0 {
		return 0, nil
	}
	var err error
	var tot int64
	todo := n
	for todo != 0 && err == nil {
		var l int64
		l, err = f.v.writeToAtMost(f.packedTapWriter(w), todo)
		if todo > 0 {
			todo -= l
		}
		tot += int64(l)
		if err == nil && todo != 0 {
			if cerr := f.finishPackedBlock(); cerr != nil {
				return tot, cerr
			}
			err = f.nextBlock()
		}
	}
	if err == io.EOF {
		if cerr := f.finishPackedBlock(); cerr != nil {
			return tot, cerr
		}
		if todo <= 0 {
			err = nil
		}
	}
	return tot, err
}

func (f *packedFileReader) WriteTo(w io.Writer) (int64, error) {
	return f.writeToN(w, -1)
}

func (pr *packedFileReader) newArchiveFileFrom(r archiveFile, blocks *fileBlockList) (archiveFile, error) {
	h := blocks.firstBlock()
	err := pr.init(blocks)
	if err != nil {
		return nil, err
	}
	if len(h.errs) > 0 {
		if len(h.errs) == 1 {
			err = h.errs[0]
		} else {
			err = errors.Join(h.errs...)
		}
		return &errorFile{archiveFile: r, err: err}, nil
	}
	if h.Encrypted {
		if h.key == nil {
			return &errorFile{archiveFile: r, err: ErrArchivedFileEncrypted}, nil
		}
		r, err = newAesDecryptFileReader(r, h.key, h.iv) // decrypt
		if err != nil {
			return nil, err
		}
	}
	// check for compression
	if h.decVer != decodeNone {
		if pr.dr == nil {
			pr.dr = new(decodeReader)
		}
		// doesn't make sense for the dictionary to be larger than the file
		if !h.Solid && !h.UnKnownSize && h.winSize > h.UnPackedSize {
			h.winSize = h.UnPackedSize
		}
		if h.winSize > maxDictSize || h.winSize > pr.opt.maxDictSize {
			return nil, ErrDictionaryTooLarge
		}
		if h.winSize > math.MaxInt {
			return nil, ErrPlatformIntSize
		}
		err := pr.dr.init(r, h.decVer, int(h.winSize), !h.Solid, h.arcSolid, h.UnPackedSize)
		if err != nil {
			return nil, err
		}
		r = pr.dr
	}
	if h.UnPackedSize >= 0 && !h.UnKnownSize {
		// Limit reading to UnPackedSize as there may be padding
		r = newLimitedReader(r, h.UnPackedSize)
	}
	if !pr.opt.skipCheck {
		var checks []fileChecksum
		if h.hash != nil {
			checks = append(checks, fileChecksum{kind: checksumCRC32, hash: h.hash()})
		}
		if h.blake2 != nil {
			checks = append(checks, fileChecksum{kind: checksumBLAKE2, hash: h.blake2()})
		}
		if len(checks) > 0 {
			r = newChecksumReader(r, checks, blocks.removeFileHash)
		}
	}
	return r, nil
}

func (pr *packedFileReader) newArchiveFile(blocks *fileBlockList) (archiveFile, error) {
	return pr.newArchiveFileFrom(pr, blocks)
}

type packedFileReadSeeker struct {
	packedFileReader
}

func (f *packedFileReadSeeker) openBlock(h *fileBlockHeader, offset int64) (int64, error) {
	err := f.v.openBlock(h.volnum, h.dataOff+offset, h.PackedSize-offset)
	if err != nil {
		return 0, err
	}
	f.h = h
	f.offset = h.packedOff + offset
	f.resetPackedChecks()
	// packed bytes before the seek offset are not hashed again
	f.pcRead = offset
	if offset != 0 {
		f.pcOn = false
	}
	return f.offset, nil
}

func (f *packedFileReadSeeker) openNextBlock(h *fileBlockHeader) error {
	_, err := f.openBlock(h, h.PackedSize)
	if err != nil {
		return err
	}
	return f.nextBlock()
}

func (f *packedFileReadSeeker) packedSize() (int64, error) {
	h := f.blocks.lastBlock()
	if h.last {
		return h.packedOff + h.PackedSize, nil
	}
	err := f.openNextBlock(h)
	for err == nil {
		err = f.nextBlock()
	}
	if err != io.EOF {
		return 0, err
	}
	if !f.h.last {
		return 0, ErrInvalidFileBlock
	}
	return f.h.packedOff + f.h.PackedSize, nil
}

func (f *packedFileReadSeeker) Seek(offset int64, whence int) (int64, error) {
	// calculate absolute offset
	switch whence {
	case io.SeekStart:
	case io.SeekCurrent:
		offset += f.offset
	case io.SeekEnd:
		size, err := f.packedSize()
		if err != nil {
			return 0, err
		}
		offset += size
	default:
		return 0, fs.ErrInvalid
	}
	if offset < 0 {
		return 0, fs.ErrInvalid
	}
	// find block in existing list
	h := f.blocks.findBlock(offset)
	if h != nil {
		offset -= h.packedOff
		return f.openBlock(h, offset)
	}
	h = f.blocks.lastBlock()
	if h.last {
		return 0, fs.ErrInvalid
	}
	err := f.openNextBlock(h)
	for err == nil {
		off := offset - h.packedOff
		if off < f.h.PackedSize || (off == f.h.PackedSize && f.h.last) {
			return f.openBlock(f.h, off)
		} else if h.last {
			return 0, fs.ErrInvalid
		}
		err = f.nextBlock()
	}
	if err == io.EOF {
		return 0, fs.ErrInvalid
	}
	return 0, err
}

func (pr *packedFileReadSeeker) newArchiveFile(blocks *fileBlockList) (archiveFile, error) {
	return pr.newArchiveFileFrom(pr, blocks)
}

func newPackedFileReader(v volume, opts *options) archiveFile {
	pr := packedFileReader{v: v, opt: opts}
	if v.canSeek() {
		return &packedFileReadSeeker{pr}
	}
	return &pr
}

type limitedReader struct {
	archiveFile
	size   int64
	offset int64
}

func (l *limitedReader) Read(p []byte) (int, error) {
	diff := l.size - l.offset
	if diff <= 0 {
		return 0, io.EOF
	}
	if int64(len(p)) > diff {
		p = p[0:diff]
	}
	n, err := l.archiveFile.Read(p)
	l.offset += int64(n)
	if err == io.EOF {
		if l.offset < l.size {
			return n, ErrShortFile
		}
		return n, nil
	}
	return n, err
}

func (l *limitedReader) ReadByte() (byte, error) {
	if l.offset >= l.size {
		return 0, io.EOF
	}
	b, err := l.archiveFile.ReadByte()
	if err != nil {
		if err == io.EOF {
			return 0, ErrShortFile
		}
		return 0, err
	}
	l.offset++
	return b, nil
}

func (l *limitedReader) writeToN(w io.Writer, n int64) (int64, error) {
	diff := l.size - l.offset
	m, err := l.archiveFile.writeToN(w, min(diff, n))
	l.offset += m
	if m < n && err == nil {
		err = io.EOF
	}
	return m, err
}

func (l *limitedReader) WriteTo(w io.Writer) (int64, error) {
	diff := l.size - l.offset
	n, err := l.archiveFile.writeToN(w, diff)
	l.offset += n
	return n, err
}

type limitedReadSeeker struct {
	limitedReader
	sr io.Seeker
}

func (l *limitedReadSeeker) Seek(offset int64, whence int) (int64, error) {
	// calculate absolute offset
	switch whence {
	case io.SeekStart:
	case io.SeekCurrent:
		offset += l.offset
	case io.SeekEnd:
		offset += l.size
	default:
		return 0, fs.ErrInvalid
	}
	if offset < 0 || offset > l.size {
		return 0, fs.ErrInvalid
	}
	return l.sr.Seek(offset, io.SeekStart)
}

func newLimitedReader(f archiveFile, size int64) archiveFile {
	lr := limitedReader{archiveFile: f, size: size}
	if sr, ok := f.(io.Seeker); ok {
		return &limitedReadSeeker{limitedReader: lr, sr: sr}
	}
	return &lr
}

type checksumKind int

const (
	checksumCRC32 checksumKind = iota
	checksumBLAKE2
)

// fileChecksum is a single declared unpacked file checksum.
type fileChecksum struct {
	kind checksumKind
	hash hash.Hash
}

// expected returns the digest declared for the checksum by the last file
// block header.
func (c fileChecksum) expected(h *fileBlockHeader) []byte {
	if c.kind == checksumCRC32 {
		return h.sum
	}
	return h.blake2sum
}

type checksumReader struct {
	archiveFile
	checks  []fileChecksum
	success func()
	eofErr  error
}

// convertHashToMAC transforms a calculated file checksum with the optional
// encryption hash key, as required by the RAR 5.0 file encryption record.
// CRC32 checksums use the XOR folded 32 bit HMAC-SHA256, BLAKE2sp checksums
// use the full 32 byte HMAC-SHA256.
func convertHashToMAC(sum, key []byte) []byte {
	mac := hmac.New(sha256.New, key)
	_, _ = mac.Write(sum) // ignore error, should always succeed
	digest := mac.Sum(nil)
	if len(sum) == 4 {
		// CRC32: fold the 32 byte HMAC into 4 bytes with XOR
		folded := make([]byte, 4)
		for i, v := range digest {
			folded[i&3] ^= v
		}
		return folded
	}
	return digest[:len(sum)]
}

func (cr *checksumReader) eofError() error {
	if cr.eofErr != nil {
		return cr.eofErr
	}
	// calculate file checksums
	h := cr.currFile()
	ok := true
	for _, c := range cr.checks {
		sum := c.hash.Sum(nil)
		if len(h.hashKey) > 0 {
			sum = convertHashToMAC(sum, h.hashKey)
		}
		if !bytes.Equal(sum, c.expected(h)) {
			ok = false
		}
	}
	if !ok {
		cr.eofErr = ErrBadFileChecksum
	} else {
		cr.eofErr = io.EOF
		if cr.success != nil {
			cr.success()
		}
	}
	return cr.eofErr
}

func (cr *checksumReader) writeChecksums(p []byte) error {
	for _, c := range cr.checks {
		if _, err := c.hash.Write(p); err != nil {
			return err
		}
	}
	return nil
}

func (cr *checksumReader) Read(p []byte) (int, error) {
	n, err := cr.archiveFile.Read(p)
	if n > 0 {
		if werr := cr.writeChecksums(p[:n]); werr != nil {
			return n, werr
		}
	}
	if err != io.EOF {
		return n, err
	}
	return n, cr.eofError()
}

func (cr *checksumReader) ReadByte() (byte, error) {
	b, err := cr.archiveFile.ReadByte()
	if err != nil {
		if err != io.EOF {
			return 0, err
		}
		return 0, cr.eofError()
	}
	if werr := cr.writeChecksums([]byte{b}); werr != nil {
		return 0, werr
	}
	return b, err
}

func (cr *checksumReader) writeToN(w io.Writer, n int64) (int64, error) {
	panic("checksumReader.writeToN should never be called")
}

func (cr *checksumReader) WriteTo(w io.Writer) (int64, error) {
	writers := make([]io.Writer, 0, len(cr.checks)+1)
	writers = append(writers, w)
	for _, c := range cr.checks {
		writers = append(writers, c.hash)
	}
	mw := io.MultiWriter(writers...)
	n, err := cr.archiveFile.WriteTo(mw)
	if err == nil || err == io.EOF {
		err = cr.eofError()
	}
	if err != nil && err != io.EOF {
		return n, err
	}
	return n, nil
}

func newChecksumReader(f archiveFile, checks []fileChecksum, success func()) *checksumReader {
	return &checksumReader{archiveFile: f, checks: checks, success: success}
}

// Reader provides sequential access to files in a RAR archive.
type Reader struct {
	f archiveFile
}

func (r *Reader) Read(p []byte) (int, error)         { return r.f.Read(p) }
func (r *Reader) ReadByte() (byte, error)            { return r.f.ReadByte() }
func (r *Reader) WriteTo(w io.Writer) (int64, error) { return r.f.WriteTo(w) }

// Next advances to the next file in the archive.
func (r *Reader) Next() (*FileHeader, error) {
	blocks, err := r.f.nextFile()
	if err != nil {
		return nil, err
	}
	r.f, err = r.f.newArchiveFile(blocks)
	if err != nil {
		return nil, err
	}
	h := blocks.firstBlock()
	return &h.FileHeader, nil
}

func newReader(v volume, opts *options) Reader {
	pr := newPackedFileReader(v, opts)
	return Reader{f: pr}
}

// NewReader creates a Reader reading from r.
// NewReader only supports single volume archives.
// Multi-volume archives must use OpenReader.
func NewReader(r io.Reader, opts ...Option) (*Reader, error) {
	options := getOptions(opts)
	v, err := newVolume(r, options, 0)
	if err != nil {
		return nil, err
	}
	rdr := newReader(v, options)
	return &rdr, nil
}

// ReadCloser is a Reader that allows closing of the rar archive.
type ReadCloser struct {
	Reader
	cl io.Closer
	vm *volumeManager
}

// Close closes the rar file.
func (rc *ReadCloser) Close() error { return rc.cl.Close() }

// Volumes returns the volume filenames that have been used in decoding the archive
// up to this point. This will include the current open volume if the archive is still
// being processed.
func (rc *ReadCloser) Volumes() []string {
	return rc.vm.Files()
}

// OpenReader opens a RAR archive specified by the name and returns a ReadCloser.
func OpenReader(name string, opts ...Option) (*ReadCloser, error) {
	options := getOptions(opts)
	v, err := openVolume(name, options)
	if err != nil {
		return nil, err
	}
	rc := &ReadCloser{vm: v.vm, cl: v}
	rc.Reader = newReader(v, options)
	return rc, nil
}

// File represents a file in a RAR archive
type File struct {
	FileHeader
	blocks *fileBlockList
	vm     *volumeManager
}

// Open returns an io.ReadCloser that provides access to the File's contents.
// Open is not supported on Solid File's as their contents depend on the decoding
// of the preceding files in the archive. Use OpenReader and Next to access Solid file
// contents instead.
func (f *File) Open() (io.ReadCloser, error) {
	return f.vm.openArchiveFile(f.blocks)
}

// List returns a list of File's in the RAR archive specified by name.
func List(name string, opts ...Option) ([]*File, error) {
	vm, fileBlocks, err := listFileBlocks(name, opts)
	if err != nil {
		return nil, err
	}
	var fl []*File
	for _, blocks := range fileBlocks {
		h := blocks.firstBlock()
		f := &File{
			FileHeader: h.FileHeader,
			blocks:     blocks,
			vm:         vm,
		}
		fl = append(fl, f)
	}
	return fl, nil
}
