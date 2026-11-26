#!/usr/bin/env python3
"""Verify the universal two-layer AND frame for bilinear maps over F_2.

Standard library only (Python 3.10+).  Run:  python3 verify.py [--deep]

A *frame* of shape (nx, ny, d) with m second-layer gates and t products is
    products     p_j = xi_j(x) * eta_j(y)                    (j < t)
    second layer h_i = lam_i(x) * sum_{j : Q[i][j] = 1} p_j  (i < m)
    outputs      out_a = sum_{i : a in c_i} h_i              (a < d)
where xi, eta, lam are linear forms (bit masks) and c_i is a set of outputs
(bit mask).  Only the 0/1 wiring matrix Q depends on the target map.  The
circuit uses exactly t + m AND gates; everything else is XOR.

Checks:
  1. type A (2,2,2; m=3,t=4) and type B (2,2,2; m=4,t=3) compute all 2^8
     bilinear maps of their shape (exhaustive, as Boolean functions);
  2. their product, the base frame (4,4,4; 12,12), computes all 64 basis
     tensors with the explicit wiring, on all 256 inputs, so by linearity in
     Q it computes all 2^64 bilinear maps F_2^4 x F_2^4 -> F_2^4; Gaussian
     elimination confirms the wiring is unique (rank 144);
  3. the tensor square (16,16,16; 144,144) computes random dense targets,
     checked exactly as reduced polynomials (equivalent to all 2^32 inputs);
     with --deep also the cube (64,64,64; 1728,1728) on random inputs;
  4. the integer inequalities used in the counting argument.
"""
import random
import sys

RNG = random.Random(20261126)


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


# ---------------------------------------------------------------- frames

class Frame:
    def __init__(self, nx, ny, d, lam, c, xi, eta):
        self.nx, self.ny, self.d = nx, ny, d
        self.lam, self.c, self.xi, self.eta = lam, c, xi, eta
        self.m, self.t = len(lam), len(xi)

    def shape(self):
        return (self.nx, self.ny, self.d, self.m, self.t)


def kron_mask(m1, m2, n2):
    out = 0
    for b1 in bits(m1):
        out |= m2 << (b1 * n2)
    return out


def kron_frame(f1, f2):
    lam = [kron_mask(a, b, f2.nx) for a in f1.lam for b in f2.lam]
    c = [kron_mask(a, b, f2.d) for a in f1.c for b in f2.c]
    xi = [kron_mask(a, b, f2.nx) for a in f1.xi for b in f2.xi]
    eta = [kron_mask(a, b, f2.ny) for a in f1.eta for b in f2.eta]
    return Frame(f1.nx * f2.nx, f1.ny * f2.ny, f1.d * f2.d, lam, c, xi, eta)


def kron_wiring(q1, q2, t2):
    """Rows are bit masks over products; returns the Kronecker product."""
    return [kron_mask(r1, r2, t2) for r1 in q1 for r2 in q2]


# Type A, shape (2, 2, 2): gates (x1; out1), (x2; out2), (x1+x2; out1+out2),
# products x_k y_s for all k, s (product index j = 2k + s).
TYPE_A = Frame(2, 2, 2, lam=[1, 2, 3], c=[1, 2, 3],
               xi=[1, 1, 2, 2], eta=[1, 2, 1, 2])
# Type B, shape (2, 2, 2): products x1y1, x2y2, (x1+x2)(y1+y2);
# gates (x_u; out a) with gate index i = 2a + u.
TYPE_B = Frame(2, 2, 2, lam=[1, 2, 1, 2], c=[1, 1, 2, 2],
               xi=[1, 2, 3], eta=[1, 2, 3])


def target_entry(phi, k, s, a, ny, d):
    """phi is a bit mask over index (k*ny + s)*d + a."""
    return (phi >> ((k * ny + s) * d + a)) & 1


def wiring_A(phi):
    """Explicit wiring for type A (see PROOF.md, Lemma 2)."""
    def form(a, k):   # the linear form in y multiplying x_k in output a
        return [target_entry(phi, k, s, a, 2, 2) for s in range(2)]

    def bil(av, bv):  # q = x1*a(y) + x2*b(y) as a mask over products j = 2k+s
        return sum(av[s] << s for s in range(2)) | sum(bv[s] << (2 + s) for s in range(2))

    def add(u, v):
        return [p ^ q for p, q in zip(u, v)]

    al1, be1, al2, be2 = form(0, 0), form(0, 1), form(1, 0), form(1, 1)
    a3, b3 = al2, be1
    a1, b1 = add(al1, al2), add(al2, be1)
    a2, b2 = add(al2, be1), add(be1, be2)
    return [bil(a1, b1), bil(a2, b2), bil(a3, b3)]


def wiring_B(phi, d=2):
    """Explicit wiring for type B (see PROOF.md, Lemma 3)."""
    full = 0b111  # p1 + p2 + p3 = x1 y2 + x2 y1
    rows = []
    for a in range(d):
        f = lambda k, s: target_entry(phi, k, s, a, 2, d)
        g1 = (f(0, 0) * 0b001) ^ (f(0, 1) * full) ^ (f(1, 0) * 0b010)
        g2 = (f(1, 1) * 0b010) ^ (f(1, 0) * full) ^ (f(0, 1) * 0b001)
        rows += [g1, g2]
    return rows


# ------------------------------------------------------------- evaluation

def evaluate(frame, q, x, y):
    """x, y are bit masks; returns the output bit mask."""
    prods = 0
    for j in range(frame.t):
        if (bin(frame.xi[j] & x).count("1") & 1) and (bin(frame.eta[j] & y).count("1") & 1):
            prods |= 1 << j
    out = 0
    for i in range(frame.m):
        if (bin(frame.lam[i] & x).count("1") & 1) and (bin(q[i] & prods).count("1") & 1):
            out ^= frame.c[i]
    return out


def bilinear_value(phi, nx, ny, d, x, y):
    out = 0
    for k in bits(x):
        for s in bits(y):
            row = (phi >> ((k * ny + s) * d)) & ((1 << d) - 1)
            out ^= row
    return out


def exhaustive_check(frame, q, phi):
    for x in range(1 << frame.nx):
        for y in range(1 << frame.ny):
            if evaluate(frame, q, x, y) != bilinear_value(phi, frame.nx, frame.ny, frame.d, x, y):
                return False
    return True


def output_polynomials(frame, q):
    """Exact reduced polynomials of the outputs (x_k^2 = x_k).

    Monomial index: (k*nx + l)*ny + s with k <= l; k == l stands for x_k y_s.
    Returns one bit mask per output.
    """
    nx, ny = frame.nx, frame.ny
    pmask = []
    for j in range(frame.t):
        m = 0
        for l in bits(frame.xi[j]):
            m |= frame.eta[j] << (l * ny)
        pmask.append(m)
    outs = [0] * frame.d
    for i in range(frame.m):
        qi = 0
        for j in bits(q[i]):
            qi ^= pmask[j]
        h = 0
        for k in bits(frame.lam[i]):
            for ls in bits(qi):
                l, s = divmod(ls, ny)
                a, b = (k, l) if k <= l else (l, k)
                h ^= 1 << ((a * nx + b) * ny + s)
        for a in bits(frame.c[i]):
            outs[a] ^= h
    return outs


def polynomial_check(frame, q, phi):
    outs = output_polynomials(frame, q)
    nx, ny, d = frame.nx, frame.ny, frame.d
    for a in range(d):
        want = 0
        for k in range(nx):
            for s in range(ny):
                if target_entry(phi, k, s, a, ny, d):
                    want |= 1 << ((k * nx + k) * ny + s)
        if outs[a] != want:
            return False
    return True


# ------------------------------------------------------------- base frame

BASE = kron_frame(TYPE_A, TYPE_B)          # shape (4, 4, 4), m = 12, t = 12


def basis_index(k, s, a, ny, d):
    return (k * ny + s) * d + a


def split_basis(k, s, a):
    """Split a basis tensor of shape (4,4,4) into its type A and type B parts."""
    (k1, k2), (s1, s2), (a1, a2) = divmod(k, 2), divmod(s, 2), divmod(a, 2)
    return 1 << basis_index(k1, s1, a1, 2, 2), 1 << basis_index(k2, s2, a2, 2, 2)


def base_wiring_basis(k, s, a):
    pa, pb = split_basis(k, s, a)
    return kron_wiring(wiring_A(pa), wiring_B(pb), TYPE_B.t)


BASE_Q = {(k, s, a): base_wiring_basis(k, s, a)
          for k in range(4) for s in range(4) for a in range(4)}


def base_wiring(phi):
    q = [0] * BASE.m
    for (k, s, a), qb in BASE_Q.items():
        if target_entry(phi, k, s, a, 4, 4):
            q = [u ^ v for u, v in zip(q, qb)]
    return q


def power_frame(n):
    f = BASE
    for _ in range(n - 1):
        f = kron_frame(f, BASE)
    return f


def power_wiring(phi, n):
    """Wiring of BASE^{(x)n} for a target phi of shape (4^n, 4^n, 4^n).

    Recursively: phi = sum_b e_b (x) phi_b with b a basis tensor of the first
    factor, and Q = sum_b Q_b (x) Q(phi_b).
    """
    if n == 1:
        return base_wiring(phi)
    ny_rest, d_rest = 4 ** (n - 1), 4 ** (n - 1)
    nx_rest = ny_rest
    rest_frame_t = 12 ** (n - 1)
    q = None
    for k in range(4):
        for s in range(4):
            for a in range(4):
                sub = 0
                for kr in range(nx_rest):
                    for sr in range(ny_rest):
                        for ar in range(d_rest):
                            K, S, A = k * nx_rest + kr, s * ny_rest + sr, a * d_rest + ar
                            if target_entry(phi, K, S, A, 4 ** n, 4 ** n):
                                sub |= 1 << basis_index(kr, sr, ar, ny_rest, d_rest)
                if not sub:
                    continue
                part = kron_wiring(BASE_Q[(k, s, a)], power_wiring(sub, n - 1), rest_frame_t)
                q = part if q is None else [u ^ v for u, v in zip(q, part)]
    return q if q is not None else [0] * (12 ** n)


# --------------------------------------------------- linear algebra (F_2)

def rank_and_solvable(rows, rhs_list):
    """rows: equations as bit masks over unknowns; rhs_list: list of rhs bit
    vectors (bit e = right-hand side of equation e). Returns rank and whether
    each system is consistent."""
    piv = []  # (pivot bit, row mask, rhs mask over systems)
    nsys = len(rhs_list)
    aug = []
    for e, r in enumerate(rows):
        rhs = 0
        for t_, v in enumerate(rhs_list):
            rhs |= ((v >> e) & 1) << t_
        aug.append([r, rhs])
    rank = 0
    inconsistent = 0
    basis = {}
    for r, rhs in aug:
        while r:
            p = r.bit_length() - 1
            if p in basis:
                br, brhs = basis[p]
                r ^= br
                rhs ^= brhs
            else:
                basis[p] = (r, rhs)
                rank += 1
                break
        else:
            inconsistent |= rhs
    return rank, [not ((inconsistent >> t_) & 1) for t_ in range(nsys)]


def gaussian_uniqueness(frame):
    """Q -> Omega is linear; equations: Omega symmetric in (k,l), diagonal = target."""
    nx, ny, d, m, t = frame.shape()
    rows = []
    keys = []
    for k in range(nx):
        for l in range(k, nx):
            for s in range(ny):
                for a in range(d):
                    mask = 0
                    for i in range(m):
                        if not (frame.c[i] >> a) & 1:
                            continue
                        for j in range(t):
                            if not (frame.eta[j] >> s) & 1:
                                continue
                            v = ((frame.lam[i] >> k) & 1) & ((frame.xi[j] >> l) & 1)
                            if k != l:
                                v ^= ((frame.lam[i] >> l) & 1) & ((frame.xi[j] >> k) & 1)
                            if v:
                                mask |= 1 << (i * t + j)
                    rows.append(mask)
                    keys.append((k, l, s, a))
    rhs_list = []
    for kb in range(nx):
        for sb in range(ny):
            for ab in range(d):
                v = 0
                for e, (k, l, s, a) in enumerate(keys):
                    if k == l == kb and s == sb and a == ab:
                        v |= 1 << e
                rhs_list.append(v)
    return len(rows), rank_and_solvable(rows, rhs_list)


# ------------------------------------------------------------------ main

def main():
    deep = "--deep" in sys.argv[1:]
    ok = True

    def report(name, cond):
        nonlocal ok
        ok &= cond
        print(f"[{'ok' if cond else 'FAIL'}] {name}")

    # 1. the two 2x2x2 frames, all 256 targets each, all 16 inputs
    report("type A (2,2,2; m=3, t=4) computes all 256 bilinear maps",
           all(exhaustive_check(TYPE_A, wiring_A(phi), phi) for phi in range(256)))
    report("type B (2,2,2; m=4, t=3) computes all 256 bilinear maps",
           all(exhaustive_check(TYPE_B, wiring_B(phi), phi) for phi in range(256)))

    # 2. base frame (4,4,4; 12,12)
    report(f"base frame has shape {BASE.shape()[:3]}, m = {BASE.m}, t = {BASE.t}",
           BASE.shape() == (4, 4, 4, 12, 12))
    report("base frame: all 64 basis tensors correct on all 256 inputs",
           all(exhaustive_check(BASE, BASE_Q[(k, s, a)], 1 << basis_index(k, s, a, 4, 4))
               for k in range(4) for s in range(4) for a in range(4)))
    report("base frame: 64 basis tensors also correct as exact polynomials",
           all(polynomial_check(BASE, BASE_Q[(k, s, a)], 1 << basis_index(k, s, a, 4, 4))
               for k in range(4) for s in range(4) for a in range(4)))
    sample = [RNG.getrandbits(64) for _ in range(200)]
    report("base frame: 200 random targets correct on all 256 inputs",
           all(exhaustive_check(BASE, base_wiring(phi), phi) for phi in sample))
    neq, (rank, solv) = gaussian_uniqueness(BASE)
    report(f"base frame: linear system has {neq} equations in 144 unknowns, rank {rank}, "
           f"all 64 basis targets solvable (wiring unique)",
           rank == 144 and all(solv))

    # 3. tensor powers
    sq = power_frame(2)
    report(f"square frame has shape {sq.shape()[:3]}, m = {sq.m}, t = {sq.t}",
           sq.shape() == (16, 16, 16, 144, 144))
    good = True
    for _ in range(3):
        phi = RNG.getrandbits(16 ** 3)
        good &= polynomial_check(sq, power_wiring(phi, 2), phi)
    report("square frame: 3 random dense targets correct as exact polynomials", good)
    if deep:
        cube = power_frame(3)
        phi = RNG.getrandbits(64 ** 3)
        q = power_wiring(phi, 3)
        good = all(evaluate(cube, q, x, y) == bilinear_value(phi, 64, 64, 64, x, y)
                   for x, y in ((RNG.getrandbits(64), RNG.getrandbits(64)) for _ in range(300)))
        report("cube frame (64,64,64; 1728,1728): random target on 300 random inputs", good)

    # 4. counting inequalities (n = 4^N)
    def first(pred):
        return next(N for N in range(1, 100) if pred(N))
    report("2*12^N < 16^N/3 holds exactly from N = 7", first(lambda N: 3 * 2 * 12 ** N < 16 ** N) == 7
           and all(3 * 2 * 12 ** N < 16 ** N for N in range(7, 60)))
    report("2*12^N < 16^N/6 holds exactly from N = 9", first(lambda N: 6 * 2 * 12 ** N < 16 ** N) == 9
           and all(6 * 2 * 12 ** N < 16 ** N for N in range(9, 60)))
    report("n = 4^N gives n^2 = 1 mod 3 and 3n(n^2-1)/3 = n^3 - n (counting bound 2^-n)",
           all((4 ** N) ** 2 % 3 == 1 for N in range(1, 40)))

    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
