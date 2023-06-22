package polymurhash

import (
	"encoding/binary"
	"math/bits"
)

type uint128 struct {
	lo, hi uint64
}

func add128(a, b uint128) uint128 {
	lo, c := bits.Add64(a.lo, b.lo, 0)
	hi := a.hi + b.hi + c
	return uint128{lo: lo, hi: hi}
}

func mul128(a, b uint64) uint128 {
	hi, lo := bits.Mul64(a, b)
	return uint128{lo: lo, hi: hi}
}

const p611 = (1 << 61) - 1

func red611(x uint128) uint64 {
	return x.lo&p611 + (x.lo>>61 | x.hi<<3)
}

func extrared611(x uint64) uint64 {
	return x&p611 + x>>61
}

const (
	arbitrary1 = 0x6a09e667f3bcc908 // Completely arbitrary, these
	arbitrary2 = 0xbb67ae8584caa73b // are taken from SHA-2, and
	arbitrary3 = 0x3c6ef372fe94f82b // are the fractional bits of
	arbitrary4 = 0xa54ff53a5f1d36f1 // sqrt(p), p = 2, 3, 5, 7.
)

func mix(x uint64) uint64 {
	x ^= x >> 32
	x *= 0xe9846af9b1a615d
	x ^= x >> 32
	x *= 0xe9846af9b1a615d
	x ^= x >> 28
	return x
}

func leUint64(b []byte) uint64 {
	l := uint64(len(b))
	if l < 4 {
		v := uint64(b[0])
		v |= uint64(b[l/2]) << (8 * (l / 2))
		v |= uint64(b[l-1]) << (8 * (l - 1))
		return v
	}
	lo := binary.LittleEndian.Uint32(b)
	hi := binary.LittleEndian.Uint32(b[l-4:])
	return uint64(lo) | (uint64(hi) << (8 * (l - 4)))
}

type Param struct {
	k, k2, k7, s uint64
}

func New(kSeed, sSeed uint64) Param {
	s := sSeed ^ arbitrary1
	var pow37 [64]uint64
	pow37[0] = 37
	pow37[32] = 559096694736811184
	for i := 0; i < 31; i++ {
		pow37[i+1] = extrared611(red611(mul128(pow37[i], pow37[i])))
		pow37[i+33] = extrared611(red611(mul128(pow37[i+32], pow37[i+32])))
	}
	for {
		kSeed += arbitrary2
		e := kSeed>>3 | 1
		if e%3 == 0 {
			continue
		}
		if e%5 == 0 || e%7 == 0 {
			continue
		}
		if e%11 == 0 || e%13 == 0 || e%31 == 0 {
			continue
		}
		if e%41 == 0 || e%61 == 0 || e%151 == 0 || e%331 == 0 || e%1321 == 0 {
			continue
		}
		ka, kb := uint64(1), uint64(1)
		for i := 0; e != 0; e >>= 2 {
			if e&1 != 0 {
				ka = extrared611(red611(mul128(ka, pow37[i])))
			}
			if e&2 != 0 {
				kb = extrared611(red611(mul128(kb, pow37[i+1])))
			}
			i += 2
		}
		k := extrared611(extrared611(red611(mul128(ka, kb))))
		k2 := extrared611(red611(mul128(k, k)))
		k3 := red611(mul128(k, k2))
		k4 := red611(mul128(k2, k2))
		k7 := extrared611(red611(mul128(k3, k4)))
		if k7 < (1<<60)-(1<<56) {
			return Param{
				k:  k,
				k2: k2,
				k7: k7,
				s:  s,
			}
		}
	}
}

func From(seed uint64) Param {
	return New(mix(seed+arbitrary3), mix(seed+arbitrary4))
}

func (p Param) HashPoly611(b []byte, tweak uint64) uint64 {
	polyAcc := tweak
	if len(b) <= 7 {
		if len(b) == 0 {
			return 0
		}
		m0 := leUint64(b)
		return polyAcc + red611(mul128(p.k+m0, p.k2+uint64(len(b))))
	}
	k3 := red611(mul128(p.k, p.k2))
	k4 := red611(mul128(p.k2, p.k2))

	if len(b) >= 50 {
		k5 := extrared611(red611(mul128(p.k, k4)))
		k6 := extrared611(red611(mul128(p.k2, k4)))
		k3 = extrared611(k3)
		k4 = extrared611(k4)
		h := uint64(0)
		for {
			var m [7]uint64
			for i := range m {
				m[i] = binary.LittleEndian.Uint64(b[7*i:]) & 0x00ffffffffffffff
			}
			t0 := mul128(p.k+m[0], k6+m[1])
			t1 := mul128(p.k2+m[2], k5+m[3])
			t2 := mul128(k3+m[4], k4+m[5])
			t3 := mul128(h+m[6], p.k7)
			s := add128(add128(t0, t1), add128(t2, t3))
			h = red611(s)
			b = b[49:]
			if len(b) < 50 {
				break
			}
		}
		k14 := red611(mul128(p.k7, p.k7))
		hk14 := red611(mul128(extrared611(h), k14))
		polyAcc += extrared611(hk14)
	}
	if len(b) >= 8 {
		m0 := binary.LittleEndian.Uint64(b) & 0x00ffffffffffffff
		m1 := binary.LittleEndian.Uint64(b[(len(b)-7)/2:]) & 0x00ffffffffffffff
		m2 := binary.LittleEndian.Uint64(b[len(b)-8:]) >> 8
		t0 := mul128(p.k2+m0, p.k7+m1)
		t1 := mul128(p.k+m2, k3+uint64(len(b)))
		if len(b) <= 21 {
			return polyAcc + red611(add128(t0, t1))
		}
		m3 := binary.LittleEndian.Uint64(b[7:]) & 0x00ffffffffffffff
		m4 := binary.LittleEndian.Uint64(b[14:]) & 0x00ffffffffffffff
		m5 := binary.LittleEndian.Uint64(b[len(b)-21:]) & 0x00ffffffffffffff
		m6 := binary.LittleEndian.Uint64(b[len(b)-14:]) & 0x00ffffffffffffff
		t0r := red611(t0)
		t2 := mul128(p.k2+m3, p.k7+m4)
		t3 := mul128(t0r+m5, k4+m6)
		s := add128(add128(t1, t2), t3)
		return polyAcc + red611(s)
	}
	m0 := leUint64(b)
	return polyAcc + red611(mul128(p.k+m0, p.k2+uint64(len(b))))
}

func (p Param) Hash(b []byte, tweak uint64) uint64 {
	if len(b) == 0 {
		return 0
	}
	h := p.HashPoly611(b, tweak)
	return mix(h) + p.s
}
