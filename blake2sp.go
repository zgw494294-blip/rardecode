package rardecode

import (
	"encoding/binary"
	"hash"
)

// BLAKE2sp is the parallel BLAKE2s variant used by RAR 5.0 for file
// integrity checks. It runs 8 BLAKE2s lanes over 512 byte wide input
// stripes and combines the 8 lane digests with a root BLAKE2s instance.
//
// This is a direct port of the public domain reference implementation
// shipped in UnRAR (blake2s.cpp / blake2sp.cpp), so its parameter block
// and tree hashing semantics match the archives produced by RAR exactly.

const (
	blake2sBlockBytes = 64
	blake2sOutBytes   = 32
	blake2spLanes     = 8
	blake2spStripe    = blake2spLanes * blake2sBlockBytes // 512

	blake2DigestSize = blake2sOutBytes
)

var blake2sIV = [8]uint32{
	0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
	0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19,
}

// Message word permutations for the 10 BLAKE2s rounds.
var blake2sSigma = [10][16]byte{
	{0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
	{14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3},
	{11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4},
	{7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8},
	{9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13},
	{2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9},
	{12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11},
	{13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10},
	{6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5},
	{10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0},
}

// blake2sState is a single BLAKE2s hash lane.
type blake2sState struct {
	h        [8]uint32
	t        [2]uint32
	f        [2]uint32
	buf      [2 * blake2sBlockBytes]byte
	buflen   int
	lastNode bool
}

func blake2sRotr32(x uint32, n uint) uint32 {
	return x>>n | x<<(32-n)
}

// reset initializes the lane with the BLAKE2sp parameter block.
// nodeOffset is the lane number for leaves and 0 for the root, nodeDepth
// is 0 for leaves and 1 for the root.
func (s *blake2sState) reset(nodeOffset uint32, nodeDepth uint32) {
	*s = blake2sState{}
	s.h = blake2sIV
	// digest length 32, key length 0, fanout 8, depth 2.
	s.h[0] ^= 0x02080020
	// 48 bit little endian node offset, 8 bit node depth and 8 bit inner
	// hash length share parameter block words 2 and 3.
	s.h[2] ^= nodeOffset
	s.h[3] ^= nodeDepth<<16 | blake2sOutBytes<<24
}

func (s *blake2sState) incrementCounter(n uint32) {
	s.t[0] += n
	if s.t[0] < n {
		s.t[1]++
	}
}

func blake2sG(m, v *[16]uint32, a, b, c, d int, x, y uint32) {
	v[a] += v[b] + m[x]
	v[d] = blake2sRotr32(v[d]^v[a], 16)
	v[c] += v[d]
	v[b] = blake2sRotr32(v[b]^v[c], 12)
	v[a] += v[b] + m[y]
	v[d] = blake2sRotr32(v[d]^v[a], 8)
	v[c] += v[d]
	v[b] = blake2sRotr32(v[b]^v[c], 7)
}

func (s *blake2sState) compress(block []byte) {
	var m [16]uint32
	for i := 0; i < 16; i++ {
		m[i] = binary.LittleEndian.Uint32(block[i*4:])
	}

	var v [16]uint32
	copy(v[:8], s.h[:])
	v[8] = blake2sIV[0]
	v[9] = blake2sIV[1]
	v[10] = blake2sIV[2]
	v[11] = blake2sIV[3]
	v[12] = s.t[0] ^ blake2sIV[4]
	v[13] = s.t[1] ^ blake2sIV[5]
	v[14] = s.f[0] ^ blake2sIV[6]
	v[15] = s.f[1] ^ blake2sIV[7]

	for r := 0; r < 10; r++ {
		sigma := &blake2sSigma[r]
		blake2sG(&m, &v, 0, 4, 8, 12, uint32(sigma[0]), uint32(sigma[1]))
		blake2sG(&m, &v, 1, 5, 9, 13, uint32(sigma[2]), uint32(sigma[3]))
		blake2sG(&m, &v, 2, 6, 10, 14, uint32(sigma[4]), uint32(sigma[5]))
		blake2sG(&m, &v, 3, 7, 11, 15, uint32(sigma[6]), uint32(sigma[7]))
		blake2sG(&m, &v, 0, 5, 10, 15, uint32(sigma[8]), uint32(sigma[9]))
		blake2sG(&m, &v, 1, 6, 11, 12, uint32(sigma[10]), uint32(sigma[11]))
		blake2sG(&m, &v, 2, 7, 8, 13, uint32(sigma[12]), uint32(sigma[13]))
		blake2sG(&m, &v, 3, 4, 9, 14, uint32(sigma[14]), uint32(sigma[15]))
	}

	for i := 0; i < 8; i++ {
		s.h[i] ^= v[i] ^ v[i+8]
	}
}

func (s *blake2sState) write(p []byte) {
	for len(p) > 0 {
		left := s.buflen
		fill := 2*blake2sBlockBytes - left
		if len(p) > fill {
			copy(s.buf[left:], p[:fill])
			s.buflen += fill
			s.incrementCounter(blake2sBlockBytes)
			s.compress(s.buf[:blake2sBlockBytes])
			copy(s.buf[:], s.buf[blake2sBlockBytes:])
			s.buflen -= blake2sBlockBytes
			p = p[fill:]
		} else {
			copy(s.buf[left:], p)
			s.buflen += len(p)
			return
		}
	}
}

// sum appends the 32 byte digest to b without mutating the lane state.
func (s *blake2sState) sum(b []byte) []byte {
	cp := *s
	if cp.buflen > blake2sBlockBytes {
		cp.incrementCounter(blake2sBlockBytes)
		cp.compress(cp.buf[:blake2sBlockBytes])
		cp.buflen -= blake2sBlockBytes
		copy(cp.buf[:], cp.buf[blake2sBlockBytes:blake2sBlockBytes+cp.buflen])
	}
	cp.incrementCounter(uint32(cp.buflen))
	if cp.lastNode {
		cp.f[1] = ^uint32(0)
	}
	cp.f[0] = ^uint32(0)
	clear(cp.buf[cp.buflen:])
	cp.compress(cp.buf[:blake2sBlockBytes])

	var digest [blake2sOutBytes]byte
	for i := 0; i < 8; i++ {
		binary.LittleEndian.PutUint32(digest[i*4:], cp.h[i])
	}
	return append(b, digest[:]...)
}

// blake2spHash implements hash.Hash for BLAKE2sp.
type blake2spHash struct {
	lanes  [blake2spLanes]blake2sState
	root   blake2sState
	buf    [blake2spStripe]byte
	buflen int
}

func newBlake2sp() hash.Hash {
	h := new(blake2spHash)
	h.Reset()
	return h
}

func (h *blake2spHash) Reset() {
	*h = blake2spHash{}
	h.root.reset(0, 1)
	h.root.lastNode = true
	for i := 0; i < blake2spLanes; i++ {
		h.lanes[i].reset(uint32(i), 0)
	}
	h.lanes[blake2spLanes-1].lastNode = true
}

func (h *blake2spHash) Size() int      { return blake2sOutBytes }
func (h *blake2spHash) BlockSize() int { return blake2spStripe }

func (h *blake2spHash) Write(p []byte) (int, error) {
	n := len(p)

	// fill a pending partial stripe
	if h.buflen > 0 && len(p) >= blake2spStripe-h.buflen {
		fill := blake2spStripe - h.buflen
		copy(h.buf[h.buflen:], p[:fill])
		for i := 0; i < blake2spLanes; i++ {
			h.lanes[i].write(h.buf[i*blake2sBlockBytes : (i+1)*blake2sBlockBytes])
		}
		p = p[fill:]
		h.buflen = 0
	}

	// process whole stripes, each lane receives its 64 byte slice of
	// every 512 byte stripe
	for len(p) >= blake2spStripe {
		for i := 0; i < blake2spLanes; i++ {
			h.lanes[i].write(p[i*blake2sBlockBytes : (i+1)*blake2sBlockBytes])
		}
		p = p[blake2spStripe:]
	}

	if len(p) > 0 {
		copy(h.buf[h.buflen:], p)
		h.buflen += len(p)
	}
	return n, nil
}

func (h *blake2spHash) Sum(b []byte) []byte {
	cp := *h

	// distribute the tail buffer across the lanes
	for i := 0; i < blake2spLanes; i++ {
		if cp.buflen > i*blake2sBlockBytes {
			left := cp.buflen - i*blake2sBlockBytes
			if left > blake2sBlockBytes {
				left = blake2sBlockBytes
			}
			cp.lanes[i].write(cp.buf[i*blake2sBlockBytes : i*blake2sBlockBytes+left])
		}
	}

	// combine the lane digests with the root
	var laneDigest [blake2spLanes * blake2sOutBytes]byte
	for i := 0; i < blake2spLanes; i++ {
		cp.lanes[i].sum(laneDigest[i*blake2sOutBytes : i*blake2sOutBytes])
	}
	for i := 0; i < blake2spLanes; i++ {
		cp.root.write(laneDigest[i*blake2sOutBytes : (i+1)*blake2sOutBytes])
	}
	return cp.root.sum(b)
}
