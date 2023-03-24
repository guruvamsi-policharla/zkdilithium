# zkDilithium is Dilithium2 version 3.1 with the following changes to make
# it more friendly for STARK-based zero knowledge proofs:
#
#  1. No public key compression, thus:
#   a) Public key contains full t instead of t_1 computed with Power2Round.
#   b) Signatures do not contain the hint, nor does verification need to
#      apply it.
#   c) tr is computed by taking full t as input instead of just t_1.
#  2. We use Poseidon for all hashes computed during verification; that is:
#     those used for the challenge c, tr and mu. We use a prefix as
#     domain separator.
#  3. We change the way sampleInBall is computed, so that rejection
#     does not occur during verification.
#  4. We absorb w1 in a different order convenient for the proof.
#
# zk20Dilithium is yet another variant that changes the modulus q
# to allow for larger proofs:

#  1. q = 2^23 - 2^20 + 1 instead of 2^23 - 2^13 + 1 so that we have a
#     larger degree primitive root of unity.
#  2. The 512th PROU for NTT zeta = 3483618.
#  3. gamma2 = 2^16

import io
import random
import hashlib
from math import ceil

import numpy as np
import galois

ORIGINAL_Q = False

NBITS = 8
N = 2**NBITS

if ORIGINAL_Q:
    Q = 2**23 - 2**13 + 1
    GAMMA2 = (Q-1)//88
    ZETA = 1753
else:
    Q = 2**23 - 2**20 + 1
    GAMMA2 = (Q-1)//112
    ZETA =  pow(3, (Q-1)//512, Q) # 512th degree primitive root of unity

class Cubic:
    def __init__(self, a0, a1, a2):
        self.a0, self.a1, self.a2 = a0, a1, a2

    def __add__(self, other):
        if isinstance(other, int):
            return Cubic(
                (self.a0 + other) % Q,
                self.a1,
                self.a2,
            )
        return Cubic(
            (self.a0 + other.a0) % Q,
            (self.a1 + other.a1) % Q,
            (self.a2 + other.a2) % Q,
        )

    def __sub__(self, other):
        return Cubic(
            (self.a0 - other.a0) % Q,
            (self.a1 - other.a1) % Q,
            (self.a2 - other.a2) % Q,
        )

    if ORIGINAL_Q:
        def __mul__(self, other):
            a0, a1, a2 = self.a0, self.a1, self.a2
            if isinstance(other, int):
                return Cubic((a0*other)%Q, (a1*other)%Q, (a2*other)%Q)
            b0, b1, b2 = other.a0, other.a1, other.a2
            return Cubic(
                (a0 * b0 + 2*(a1 * b2 + a2 * b1)) % Q,
                (a0 * b1 + a1 * b0 + 2*(a2 * b2)) % Q,
                (a0 * b2 + a1 * b1 + a2 * b0) % Q,
            )
    else:
        def __mul__(self, other):
            a0, a1, a2 = self.a0, self.a1, self.a2
            if isinstance(other, int):
                return Cubic((a0*other)%Q, (a1*other)%Q, (a2*other)%Q)
            b0, b1, b2 = other.a0, other.a1, other.a2
            x3 = a2 * b1 + a1 * b2
            x4 = a2 * b2
            return Cubic(
                ((a0 * b0) + x3) % Q,
                ((a0 * b1) + (a1 * b0) - x3 + x4) % Q,
                ((a0 * b2) + (a1 * b1) + (a2 * b0) - x4) % Q,
            )
    def __str__(self):
        return f'Cubic({self.a0}, {self.a1}, {self.a2})'

class Sextic:
    def __init__(self, a0, a1):
        self.a0, self.a1 = a0, a1

    def __add__(self, other):
        if isinstance(other, int):
            return Sextic(
                self.a0 + other,
                self.a1,
            )
        return Sextic(
            self.a0 + other.a0,
            self.a1 + other.a1,
        )

    def __sub__(self, other):
        return Sextic(
            self.a0 - other.a0,
            self.a1 - other.a1,
        )

    if ORIGINAL_Q:
        def __mul__(self, other):
            a0, a1 = self.a0, self.a1
            if isinstance(other, int):
                return Sextic(a0*other, a1*other)
            b0, b1 = other.a0, other.a1
            a0b0 = a0*b0
            a1b1 = a1*b1
            a0b0_a1b1 = a0b0 + a1b1
            a1b1_x4 = a1b1 + a1b1
            a1b1_x4 = a1b1_x4 + a1b1_x4a1b1 
            return Sextic(
                a0b0_a1b1 + a1b1_x4,
                (a0 + a1)*(b0 + b1) - a0b0_a1b1,
            )
    else:
        def __mul__(self, other):
            a0, a1 = self.a0, self.a1
            if isinstance(other, int):
                return Sextic(a0*other, a1*other)
            b0, b1 = other.a0, other.a1
            a0b0 = a0*b0
            a1b1 = a1*b1
            return Sextic(
                a0b0 - a1b1 - a1b1 - a1b1,
                (a0+a1)*(b0+b1) - a0b0 - a1b1
            )

    def __str__(self):
        return f'Sextic({self.a0}, {self.a1})'


GAMMA1 = 2**17

ETA = 2
K = 4
L = 4
TAU = 40
BETA = TAU * ETA

CSIZE = 12 # number of field elements to use for c tilde
MUSIZE = 24 #                                for mu

assert GAMMA1 == 2**17
POLY_LE_GAMMA1_SIZE = 576

def inv(x):
    return pow(x, Q-2, Q)

INVZETA = inv(ZETA)
INV2 = (Q+1)//2 # inverse of 2

def brv(x):
    """ Reverses a 8-bit number. Used in the NTT. """
    return int(''.join(reversed(bin(x)[2:].zfill(NBITS))), 2)

ZETAS = [pow(ZETA, brv(i+1), Q) for i in range(N)]
INVZETAS = [pow(INVZETA, 256-brv(255-i), Q) for i in range(N)]

POS_T = 35
POS_RATE = 24
POS_RF = 21    # full rounds of Poseidon
POS_CYCLE_LEN = 8

class Grain:
    """ LSFR used to generate MDS and round constants for Poseidon """
    def __init__(self):
        self.state = (
            (2**30-1) | 
            (0 << 30) |        # 0 partial rounds
            (POS_RF << 40) |   # full rounds. TODO Does not fit in spec 
            (POS_T << 50) |    # size of state
            (POS_RATE << 62) | # rate
            (2 << 74) |        # alpha = -1
            (1 << 78)          # odd Q
        )
        for _ in range(160):
            self._next()

    def readBits(self, bits):
        got = 0
        ret = 0
        while got < bits:
            first = self._next()
            second = self._next()
            if first == 1:
                ret = (ret << 1) | second
                got += 1
        return ret

    def readFe(self):
        while True:
            x = self.readBits(23)
            if x < Q:
                return x

    def _next(self):
        s = self.state
        r = (((s >> 17) & 1) ^ ((s >> 28) & 1) ^ ((s >> 41) & 1) ^
            ((s >> 56) & 1) ^ ((s >> 66) & 1) ^ ((s >> 79) & 1))
        self.state = ((s << 1) & 0xffffffffffffffffffff) | r
        return r

# Poseidon round constants
def generate_poseidon_rcs():
    rng = Grain()
    return [rng.readFe() for i in range(POS_T * POS_RF)]

# Saving round constants
def save_poseidon_rcs(POS_RCS, MDS):
    f = open("log/poseidon_ark.txt", "w")
    f.write("ARK:\n")
    f.write("[")
    for j in range(7): # CYCLE_LENGTH-1
        f.write("[")
        for i in range(POS_T*3): # STATE_WIDTH*3 rounds in each row of AIR
            f.write("BaseElement::new("+str(POS_RCS[j*3*POS_T+i])+"), ")
        f.write("],\n")
    f.write("]\n")

    f.write("\n\n")

    f.write("MDS:\n")
    f.write("[")
    for j in range(1,POS_T+1): # CYCLE_LENGTH-1
        # f.write("[")
        for i in range(1,POS_T+1): # STATE_WIDTH*3 rounds in each row of AIR
            f.write("BaseElement::new("+str(inv(i+j-1))+"), ")
        f.write("\n")
    f.write("]\n")
    
    f.write("\n\n")
    
    GF = galois.GF(Q)
    MDS = GF([[inv(i+j-1) for i in range(1, POS_T+1)] for j in range(1, POS_T+1)])
    INV_MDS = np.linalg.inv(MDS)
    f.write("INV_MDS:\n")
    f.write("[")
    for j in range(POS_T): # CYCLE_LENGTH-1
        # f.write("[")
        for i in range(POS_T): # STATE_WIDTH*3 rounds in each row of AIR
            f.write("BaseElement::new("+str(INV_MDS[i][j])+"), ")
        f.write("\n")
    f.write("]\n")

    f.close()

POS_RCS = generate_poseidon_rcs()
POS_INV = [inv(i) for i in range(1, 2*POS_T)]
save_poseidon_rcs(POS_RCS, POS_INV)

def poseidon_round(state, r):
    # AddRoundConstants
    for i in range(POS_T):
        state[i] = (state[i] + POS_RCS[POS_T*r + i]) % Q

    # S-box
    # TODO check if batching is worth it
    for i in range(POS_T):
        state[i] = inv(state[i])

    # MDS, we use M_ij = 1/(i+j-1)
    old = tuple(state)
    for i in range(POS_T):
        acc = 0
        for j in range(POS_T):
            acc += POS_INV[i+j] * old[j]
        state[i] = acc % Q

def poseidon_perm(state):
    """ Applies the poseidon permutation to the given state in place """
    for r in range(POS_RF):
        poseidon_round(state, r)

class Poseidon:
    def __init__(self, initial=None):
        self.s = [0]*POS_T
        self.absorbing = True
        self.i = 0
        if not initial is None:
            self.write(initial)
    def write(self, fes):
        assert self.absorbing
        for fe in fes:
            self.s[self.i] = (self.s[self.i] + fe) % Q
            self.i += 1
            if self.i == POS_RATE:
                poseidon_perm(self.s)
                self.i = 0
    
    def permute(self):
        assert self.absorbing
        if self.i != 0:
            poseidon_perm(self.s)
            self.i = 0
    
    def read(self, n):
        if self.absorbing:
            self.absorbing = False
            if self.i != 0:
                poseidon_perm(self.s)
                self.i = 0
        ret = []
        while n > 0:
            to_read = min(n, POS_RATE - self.i)
            ret += self.s[self.i:self.i+to_read]
            n -= to_read
            self.i += to_read
            if self.i == POS_RATE:
                self.i = 0
                poseidon_perm(self.s)
        return ret
    def read_nomod(self, n):
        assert n <= POS_RATE
        return self.s[:n]


class Poly:
    """ Represents an element of the polynomial ring  Z_q[x]/<x^256+1>. """
    def __init__(self, cs=None):
        self.cs = (0,)*N if cs is None else tuple(cs)
        assert len(self.cs) == N

    def __add__(self, other):
        return Poly((a+b) % Q for a,b in zip(self.cs, other.cs))

    def __neg__(self):
        return Poly((Q-a)%Q for a in self.cs)

    def __sub__(self, other):
        return self + -other

    def __str__(self):
        return f"Poly({self.cs}"

    def __eq__(self, other):
        return self.cs == other.cs

    def NTT(self):
        cs = list(self.cs)
        layer = N // 2
        zi = 0
        while layer >= 1:
            for offset in range(0, N-layer, 2*layer):
                z = ZETAS[zi]
                zi += 1

                for j in range(offset, offset+layer):
                    t = (z * cs[j + layer]) % Q
                    cs[j + layer] = (cs[j] - t) % Q
                    cs[j] = (cs[j] + t) % Q
            layer //= 2
        return Poly(cs)

    def InvNTT(self):
        cs = list(self.cs)
        layer = 1
        zi = 0
        while layer < N:
            for offset in range(0, N-layer, 2*layer):
                z = INVZETAS[zi]
                zi += 1

                for j in range(offset, offset+layer):
                    t = (cs[j] - cs[j + layer]) % Q
                    cs[j] = (INV2*(cs[j] + cs[j+layer])) % Q
                    cs[j+layer] = (INV2 * z * t) % Q
            layer *= 2
        return Poly(cs)

    def MulNTT(self, other):
        """ Multiplication in the NTT domain, i.e. componentwise """
        return Poly((a*b) % Q for a,b in zip(self.cs, other.cs))

    def SchoolbookMul(self, other):
        """ Returns (q, r) such that self * other = q (x^256 + 1) + r """
        s = [sum(self.cs[j] * other.cs[i - j]
                for j in range(max(i - 255, 0), min(i + 1, 256))) % Q
                    for i in range(511)]
        s.append(0)
        q = Poly(s[256:])
        r = Poly((s[i] - s[256+i]) % Q for i in range(256))
        return (q, r)

    def pack(self):
        return packFes(self.cs)

    def packLeqEta(self):
        ret = io.BytesIO()
        cs = [(ETA-c)%Q for c in self.cs]
        for i in range(0, 256, 8):
            ret.write(bytes([
                cs[i] | (cs[i+1] << 3) | ((cs[i+2] << 6) & 255),
                (cs[i+2] >> 2) | (cs[i+3] << 1) | (cs[i+4] << 4) | ((cs[i+5] << 7) & 255),
                (cs[i+5] >> 1) | (cs[i+6] << 2) | (cs[i+7] << 5),
            ]))
        return ret.getvalue()

    def packLeGamma1(self):
        ret = io.BytesIO()
        cs = [(GAMMA1-c)%Q for c in self.cs]
        for i in range(0, 256, 4):
            ret.write(bytes([
                cs[i] & 255,
                (cs[i] >> 8) & 255,
                (cs[i] >> 16) | ((cs[i+1] << 2) & 255),
                (cs[i+1] >> 6) & 255,
                (cs[i+1] >> 14) | ((cs[i+2] << 4) & 255),
                (cs[i+2] >> 4) & 255,
                (cs[i+2] >> 12) | ((cs[i+3] << 6) & 255),
                (cs[i+3] >> 2) & 255,
                (cs[i+3] >> 10) & 255,
            ]))
        return ret.getvalue()

    def norm(self):
        n = 0
        for c in self.cs:
            if c > (Q-1)//2:
                c = Q - c
            n = max(c, n)
        return n

    def decompose(self):
        p0, p1 = [], []
        for c in self.cs:
            c0, c1 = decompose(c)
            p0.append(c0)
            p1.append(c1)
        return Poly(p0), Poly(p1)

    def eval(self, x):
        """ Evaluate this polynomial on x. """
        ret = 0 
        for i in range(N-1, -1, -1):
            ret = (x * ret) + self.cs[i]
        return ret


def packFes(fes):
    ret = io.BytesIO()
    for c in fes:
        ret.write(bytes([
            c & 255,
            (c >> 8) & 255,
            c >> 16,
        ]))
    return ret.getvalue()

def unpackFes(bs):
    cs = []
    assert len(bs) % 3 == 0
    for i in range(0, len(bs), 3):
        cs.append((bs[i] | (bs[i+1] << 8) | (bs[i+2] << 16)) % Q)
    return cs

def unpackPoly(bs):
    assert len(bs) == 256*3
    return Poly(unpackFes(bs))

def unpackPolyLeqEta(bs):
    ret = []
    for i in range(0, 96, 3):
        ret.append(bs[i] & 7)
        ret.append((bs[i] >> 3) & 7)
        ret.append((bs[i] >> 6) | ((bs[i+1] << 2) & 7))
        ret.append((bs[i+1] >> 1) & 7)
        ret.append((bs[i+1] >> 4) & 7)
        ret.append((bs[i+1] >> 7) | ((bs[i+2] << 1) & 7))
        ret.append((bs[i+2] >> 2) & 7)
        ret.append((bs[i+2] >> 5) & 7)
    return Poly((ETA - c)%Q for c in ret)
        

def unpackVecLeqEta(bs, l):
    return Vec(unpackPolyLeqEta(bs[i*256//8*3:])
               for i in range(l))


def unpackVec(bs, l):
    assert len(bs) == l * 256*3
    return Vec(unpackPoly(bs[256*3*i:256*3*(i+1)])
            for i in range(l))

assert GAMMA1 == 2**17
def unpackPolyLeGamma1(bs):
    ret = []
    for i in range(0, 64*9, 9):
        cs = [
            bs[i] | (bs[i+1] << 8) | ((bs[i+2] & 0x3) << 16),
            (bs[i+2] >> 2) | (bs[i+3] << 6) | ((bs[i+4] & 0xf) << 14),
            (bs[i+4] >> 4) | (bs[i+5] << 4) | ((bs[i+6] & 0x3f) << 12),
            (bs[i+6] >> 6) | (bs[i+7] << 2) | (bs[i+8] << 10),
        ]
        for c in cs:
            ret.append((GAMMA1 - c) % Q)
    ret = Poly(ret)
    assert ret.norm() <= GAMMA1
    return ret

def unpackVecLeGamma1(bs, l):
    assert len(bs) == l * POLY_LE_GAMMA1_SIZE
    return Vec(unpackPolyLeGamma1(
        bs[POLY_LE_GAMMA1_SIZE*i:POLY_LE_GAMMA1_SIZE*(i+1)]) for i in range(l))

class Vec:
    def __init__(self, ps):
        self.ps = tuple(ps)

    def NTT(self):
        return Vec(p.NTT() for p in self.ps)

    def InvNTT(self):
        return Vec(p.InvNTT() for p in self.ps)

    def DotNTT(self, other):
        """ Computes the dot product <self, other> in NTT domain. """
        return sum((a.MulNTT(b) for a, b in zip(self.ps, other.ps)),
                   Poly())

    def SchoolbookDot(self, other, desc=''):
        """ Computes the dot product <self, other> """
        retr = Poly()
        retq = Poly()
        for a, b in zip(self.ps, other.ps):
            q, r = a.SchoolbookMul(b)
            retr += r
            retq += q
        return (retq, retr)
    
    def SchoolbookDotDebug(self, other, desc=''):
        """ Computes the dot product <self, other> """
        retr = Poly()
        retq = Poly()
        for a, b in zip(self.ps, other.ps):
            q, r = a.SchoolbookMul(b)
            retr += r
            retq += q
        
        return (retq, retr)

    def __add__(self, other):
        return Vec(a+b for a,b in zip(self.ps, other.ps))
    def __sub__(self, other):
        return Vec(a-b for a,b in zip(self.ps, other.ps))

    def __eq__(self, other):
        return self.ps == other.ps

    def ScalarMulNTT(self, sc):
        return Vec(p.MulNTT(sc) for p in self.ps)
    
    def SchoolbookScalarMul(self, sc, desc=''):
        ret = []
        for p in self.ps:
            q, r = p.SchoolbookMul(sc)
            ret.append(r)
        return Vec(ret)
    
    def SchoolbookScalarMulDebug(self, sc, desc=''):
        retr = []
        retq = []
        for p in self.ps:
            q, r = p.SchoolbookMul(sc)
            retr.append(r)
            retq.append(q)

        return (Vec(retq), Vec(retr))

    def pack(self):
        return b''.join(p.pack() for p in self.ps)
    def packLeqEta(self):
        return b''.join(p.packLeqEta() for p in self.ps)
    def packLeGamma1(self):
        return b''.join(p.packLeGamma1() for p in self.ps)

    def decompose(self):
        v0, v1 = [], []
        for v in self.ps:
            p0, p1 = v.decompose()
            v0.append(p0)
            v1.append(p1)
        return Vec(v0), Vec(v1)

    def norm(self):
        return max(p.norm() for p in self.ps)

    def __str__(self):
        return f'Vec{[str(p) for p in self.ps]}'


class Matrix:
    def __init__(self, cs):
        """ Samples the matrix uniformly from seed rho """
        self.cs = tuple(tuple(row) for row in cs)

    def MulNTT(self, vec):
        """ Computes matrix multiplication A*vec in the NTT domain. """
        return Vec(Vec(row).DotNTT(vec) for row in self.cs)

    def SchoolbookMul(self, vec, desc=''):
        """ Compute schoolbook matrix multiplication InvNTT(A) * vec. """
        return Vec(Vec(row).InvNTT().SchoolbookDot(vec, f'({desc})_{i+1}')[1]
                   for i, row in enumerate(self.cs))
    
    def SchoolbookMulDebug(self, vec, desc=''):
        """ Debug: Compute schoolbook matrix multiplication InvNTT(A) * vec. """
        q = Vec(Vec(row).InvNTT().SchoolbookDotDebug(vec, f'(D{desc})_{i+1}')[0]
                   for i, row in enumerate(self.cs))
        
        r = Vec(Vec(row).InvNTT().SchoolbookDotDebug(vec, f'(D{desc})_{i+1}')[1]
                   for i, row in enumerate(self.cs))
        
        return (q, r)


def sampleUniform(stream):
    cs = []
    while True:
        b = stream.read(3)
        d = (b[0] + (b[1] << 8) + (b[2] << 16)) & 0x7fffff
        if d >= Q:
            continue
        cs.append(d)
        if len(cs) == N:
            return Poly(cs)

assert ETA in [2] # also update packLeqEta
def sampleLeqEta(stream):
    cs = []
    while True:
        b = stream.read(3)
        ds = [b[0] & 15, b[0] >> 4,
              b[1] & 15, b[1] >> 4,
              b[2] & 15, b[2] >> 4]
        for d in ds:
            if d <= 14:
                cs.append((2 - (d % 5)) % Q)
            if len(cs) == N:
                return Poly(cs)

def sampleMatrix(rho):
    return Matrix([[sampleUniform(XOF128(rho, 256*i + j))
            for j in range(L)] for i in range(K)])

def sampleSecret(rho):
    ps = [sampleLeqEta(XOF256(rho, i)) for i in range(K + L)]
    return Vec(ps[:L]), Vec(ps[L:])

def XOF128(seed, nonce):
    # TODO Proper streaming for SHAKE-128
    packedNonce = bytes([nonce & 255, nonce >> 8])
    return io.BytesIO(hashlib.shake_128(seed + packedNonce).digest(
        length=1344))  # needs Python >3.10
def XOF256(seed, nonce):
    # TODO Proper streaming for SHAKE-256
    packedNonce = bytes([nonce & 255, nonce >> 8])
    return io.BytesIO(hashlib.shake_256(seed + packedNonce).digest(
        length=2*136)) # needs Python >3.10

def H(msg, length):
    return hashlib.shake_256(msg).digest(length=length)

def sampleY(rho, nonce):
    return Vec(unpackPolyLeGamma1(
        hashlib.shake_256(rho + bytes([(nonce+i) & 255, (nonce+i) >> 8])).digest(
            length=256//4*9)) for i in range(L))


def decompose(r):
    r0 = r % (2*GAMMA2)
    if r0 > GAMMA2:
        r0 -= 2*GAMMA2
    if r - r0 == Q-1:
        return r0-1, 0
    return r0, (r-r0)//(2*GAMMA2)

def decompose_flag(r):
    r0 = r % (2*GAMMA2)
    if r0 > GAMMA2:
        r0 -= 2*GAMMA2
    if r - r0 == Q-1:
        return r0-1, 0
    return r0, (r-r0)//(2*GAMMA2)

def Gen(seed):
    """ Generates a keypair """
    assert len(seed) == 32
    expandedSeed = H(seed, 32 + 64 + 32)
    rho = expandedSeed[:32]
    rho2 = expandedSeed[32:32+64]
    key = expandedSeed[32+64:]
    Ahat = sampleMatrix(rho)
    s1, s2 = sampleSecret(rho2)
    t = (Ahat.MulNTT(s1.NTT()) + s2.NTT()).InvNTT()
    tPacked = t.pack()
    tr = H(rho + tPacked, 32)

    assert unpackVecLeqEta(s2.packLeqEta(), K) == s2
    assert unpackVecLeqEta(s1.packLeqEta(), L) == s1
    assert unpackVec(tPacked, K) == t

    return (
        rho + tPacked,
        rho + key + tr + s1.packLeqEta() + s2.packLeqEta() + tPacked
    )

def unpackFesLoose(bs):
    # We add 1 to each byte so that we can distinguish between b'h' and b'h\0'
    bs = [b + 1 for b in bs]
    if len(bs) & 1 == 1:
        bs.append(0)
    ret = []
    for i in range(len(bs)//2):
        ret.append(bs[2*i] + 257*bs[2*i+1])
    return ret

def bytesToFes(bs):
    # We add 1 to each byte so that we can distinguish between b'h' and b'h\0'
    bs = [b + 1 for b in bs]
    if len(bs) & 1 == 1:
        bs.append(0)
    ret = []
    for i in range(len(bs)//2):
        ret.append(bs[2*i] + 257*bs[2*i+1])
    return ret

def sampleInBall(h):
    signs = []
    ret = [0]*256
    signsPerFe = 8 # number of signs to extract per field element
    NTAU = ceil(TAU/POS_CYCLE_LEN)*POS_CYCLE_LEN
    # Debug variables
    swaps = []

    # TAU is forced to be a multiple of POS_CYCLE_LEN to simplify AIR
    for i in range(ceil(TAU/POS_CYCLE_LEN)):
        poseidon_perm(h.s)
        swaps = []
        signs = []
        # In each cycle
        # Read one field element and extract POS_CYCLE_LEN bits
        fes = h.read_nomod(9)
        fe = fes[8]
        q, r = divmod(fe, 2**signsPerFe)
        if q == Q // 2**signsPerFe:
            return None
        for j in range(signsPerFe):
            signs.append(1 if r & 1 == 0 else Q-1)
            r >>= 1
        
        # Read 8 field elements and extract POS_CYCLE_LEN swap positions
        for j in range(POS_CYCLE_LEN):
            base = 256-NTAU + i*POS_CYCLE_LEN + j
            fe = fes[j]
            q, r = divmod(fe, base+1)
            if q == Q // (base+1):
                return None
            swaps.append(r)
            ret[base] = ret[r]
            ret[r] = signs[j]

    return Poly(ret)

# TODO update after sampleInBall is fixed.
def sampleInBallSuccessProb():
    from fractions import Fraction
    ok = Fraction(1, 1)
    for i in range(5):
        ok *= (1 - Fraction(Q % 256, Q))
    for base in range(256-TAU+1, 257):
        ok *= (1 - Fraction(Q % base, Q))
    return ok

def Sign(sk, msg):
    rho = sk[:32]
    key = sk[32:32*2]
    tr = sk[32*2:32*3]
    s1 = unpackVecLeqEta(sk[32*3:32*3+96*L], L)
    s2 = unpackVecLeqEta(sk[32*3+96*L:32*3+96*(L+K)], K)
    t = unpackVec(sk[32*3+96*(L+K):], K)
    Ahat = sampleMatrix(rho)
    h = Poseidon([0])
    h.write(unpackFesLoose(tr))
    h.permute() #apply a poseidon permutation before inserting msg||com_r
    h.write(unpackFesLoose(msg)) #assumes com_r = [0]*12
    mu = h.read(MUSIZE)
    #MU IS GETTING HASHED IMMEDIATELY AFTER INSERTION BUT NOT IN THE RUST CODE. MATCH THIS
    s1Hat = s1.NTT()
    s2Hat = s2.NTT()

    yNonce = 0
    z = 0
    rho2 = H(key + H(tr + msg, 64), 64)
    while True:
        y = sampleY(rho2, yNonce)
        yNonce += L
        w = Ahat.MulNTT(y.NTT()).InvNTT()
        w0, w1 = w.decompose()

        h = Poseidon()
        h.write(mu)
        
        # Need to apply permutation here

        for j in range(N):
            for i in range(K):
                h.write([w1.ps[i].cs[j]])
        cTilde = h.read(CSIZE)

        h = Poseidon([2])
        h.write(cTilde)
        c = sampleInBall(h)
        if c is None:
            print("Retrying because of challenge")
            continue
        
        cHat = c.NTT()
        cs2 = s2Hat.ScalarMulNTT(cHat).InvNTT()

        r0, _ = (w-cs2).decompose()

        if r0.norm() >= GAMMA2 - BETA:
            print("Retrying because of r0 check")
            continue

        z = y + s1Hat.ScalarMulNTT(cHat).InvNTT()
        if z.norm() >= GAMMA1 - BETA:
            print("Retrying because of z check")
            continue

        return packFes(cTilde) + z.packLeGamma1()

def Verify(pk, msg, sig):
    if len(sig) != CSIZE*3 + POLY_LE_GAMMA1_SIZE*L:
        return False
    packedCTilde, packedZ = sig[:CSIZE*3], sig[CSIZE*3:]
    z = unpackVecLeGamma1(packedZ, L)
    cTilde = unpackFes(packedCTilde)
    rho = pk[:32]
    tPacked = pk[32:]
    t = unpackVec(tPacked, K)
    tr = H(rho + tPacked, 32)

    h = Poseidon([0])
    h.write(unpackFesLoose(tr))
    h.permute()
    h.write(unpackFesLoose(msg))
    
    mu = h.read(MUSIZE)

    c = sampleInBall(Poseidon([2] + cTilde))
    if c is None:
        return False
    cHat = c.NTT()
    if z.norm() >= GAMMA1 - BETA:
        return False
    Ahat = sampleMatrix(rho)
    zHat = z.NTT()
    tHat = t.NTT()
    _, w1 = (Ahat.MulNTT(zHat) - tHat.ScalarMulNTT(cHat)).InvNTT().decompose()

    h = Poseidon()
    h.write(mu)
    
    for j in range(N):
        for i in range(K):
            h.write([w1.ps[i].cs[j]])
    cTilde2 = h.read(CSIZE)
    if cTilde2 != cTilde:
        return False
    return True
    
def SchoolbookVerify(pk, msg, sig):
    ################# Building a testcase
    f = open("log/testcase.txt", "a")

    if len(sig) != CSIZE*3 + POLY_LE_GAMMA1_SIZE*L:
        return False
    packedCTilde, packedZ = sig[:CSIZE*3], sig[CSIZE*3:]
    z = unpackVecLeGamma1(packedZ, L)
    cTilde = unpackFes(packedCTilde)
    rho = pk[:32]
    tPacked = pk[32:]
    t = unpackVec(tPacked, K)
    tr = H(rho + tPacked, 32)
    
    h = Poseidon([0])
    h.write(bytesToFes(tr))
    h.permute()
    f.write("h_tr: \n" + str(h.s) + "\n\n")
    
    msgFes = bytesToFes(msg)
    h.write(msgFes)

    # TODO: write com_r and extend msgFes to 12 elements
    f.write("m: \n" + str(msgFes) + "\n\n")
    # f.write("com_r: \n" + str(bytesToFes(com_r)) + "\n\n")

    mu = h.read(MUSIZE)

    f.write("mu: \n" + str(mu) + "\n\n")

    c = sampleInBall(Poseidon([2] + cTilde))
    
    if c is None:
        return False
    if z.norm() >= GAMMA1 - BETA:
        return False
    
    Ahat = sampleMatrix(rho)
    zHat = z.NTT()
    _, w1 = (Ahat.SchoolbookMul(z, 'Az') - t.SchoolbookScalarMul(c, 'tc')).decompose()

    # signature
    f.write("ctilde: \n" + str(cTilde) + "\n\n")
    
    f.write("c: \n" + str(c) + "\n\n")

    f.write("z: \n")
    for i in range(4):
        f.write(str(z.ps[i])+",\n")
    f.write("\n")

    # Public key
    f.write("t: \n")
    for i in range(4):
        f.write(str(t.ps[i])+",\n")
    f.write("\n")

    f.write("A: \n" )
    for i in range(4):
        f.write("[ \n")
        for j in range(4):
            f.write(str(Ahat.cs[i][j].InvNTT())+",\n")
        f.write("] \n")
    f.write("\n")

    # Computing the witness wire values
    Azq, Azr = Ahat.SchoolbookMulDebug(z, 'Az')
    Tq, Tr = t.SchoolbookScalarMulDebug(c, 'tc')

    AzTq = Azq - Tq
    AzTr = Azr - Tr

    f.write("qw: \n")
    for i in range(4):
        f.write(str(AzTq.ps[i])+",\n")
    f.write("\n")
    
    f.write("w: \n")
    for i in range(4):
        f.write(str(AzTr.ps[i])+",\n")
    f.write("\n")

    f.close()

    # Cleanup
    with open("log/testcase.txt") as f:
        newText=f.read()\
                .replace("Poly(", "")\
                .replace("(", "[")\
                .replace(")", "]")

    with open("log/testcase.txt", "w") as f:
        f.write(newText)
    
    h = Poseidon()
    h.write(mu)
    
    for j in range(N):
        for i in range(K):
            h.write([w1.ps[i].cs[j]])
    
    cTilde2 = h.read(CSIZE)
    
    if cTilde2 != cTilde:
        return False
    return True

def test_sign():
    f = open("log/testcase.txt", "w")
    f.close()
    pk, sk = Gen(b'\0'*32)
    msg = b'test'
    sig = Sign(sk, msg)
    assert Verify(pk, msg, sig)
    assert SchoolbookVerify(pk, msg, sig)

def test_ntt():
    assert Poly([1] + [0]*255).NTT() == Poly([1]*256)
    assert Poly(range(256)).NTT().InvNTT() == Poly(range(256))

def test_schoolbook():
    a = Poly(range(256))
    b = Poly(range(256,512))
    r2 = a.NTT().MulNTT(b.NTT()).InvNTT()
    q, r = a.SchoolbookMul(b)
    assert r == r2

def test_zeta():
    assert pow(ZETA, 256, Q) == Q-1

def test_decompose():
    for r in range(Q):
        r0, r1 = decompose(r)
        assert (r1*2*GAMMA2 + r0)%Q == r
        if r >= Q - GAMMA2:
            assert -GAMMA2 <= r0
            assert r0 < 0
            assert r1 == 0
        else:
            assert -GAMMA2 < r0
            assert r0 <= GAMMA2

def test_decompose_air():
    for r in range(Q):
        r0, r1 = decompose(r)
        assert (r1*2*GAMMA2 + r0)%Q == r
        if r >= Q - GAMMA2:
            assert -GAMMA2 <= r0
            assert r0 < 0
            assert r1 == 0
        else:
            assert -GAMMA2 < r0
            assert r0 <= GAMMA2

def print_hash_state():
    with open('log/pypos.txt', 'w') as f:
        test_sign()
        state = [5333080, 210811, 6105801, 2424493, 6813730, 5433526, 1082539, 1101160, 5770059, 5916290, 6538538, 3542320, 5485586, 4199361, 6972395, 6852729, 2479000, 232810, 2256442, 4486796, 889444, 5337286, 3188483, 7311008, 2701442, 4132688, 5089133, 1249084, 4893610, 5702096, 3104718, 3030123, 4087558, 5616624, 2498572, ]
        f.write(str(state))
        f.write('\n')
        for r in range(POS_RF):
            poseidon_round(state, r)
            f.write(str(state))
            f.write('\n')

def test_pack_le_gamma1():
    for i in range(1000):
        p = Poly(random.randint(-GAMMA1+1, GAMMA1)%Q for _ in range(N))
        p2 = unpackPolyLeGamma1(p.packLeGamma1())
        assert p == p2

if __name__ == '__main__':
    test_sign()
    # import pytest
    # pytest.main(['zkdilithium.py'])