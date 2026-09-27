"""pell.py -- polynomial Pell equations and pseudo-elliptic integrals.

First piece of milestone (iii): units of O = Q[x][y]/(y^2 - q) via the
continued-fraction expansion of sqrt(q) in Q((1/x)) (Abel--Chebyshev),
and a driver for pseudo-elliptic integrals

    int N(x)/sqrt(q(x)) dx  =  gamma * log(A + B*sqrt(q))  +  V0 + V1*sqrt(q).

The unit A + B*y (A^2 - q*B^2 constant) exists iff the divisor
oo_+ - oo_- is torsion in the Jacobian; its absence within the step
bound is reported but not certified (certification = the torsion bound
of Parts I--II, a later milestone).  Element arithmetic is on the
(w_0, w_1)-coordinates, i.e. the m = 2 Trager basis (1, y) for q
squarefree; verification of the output is exact, componentwise.
"""

import math
import sympy as sp
from sympy.polys.domains import ZZ
from sympy.polys.galoistools import (gf_gcdex, gf_mul, gf_add, gf_sub, gf_rem, gf_quo,
                                     gf_monic, gf_degree, gf_strip, gf_neg, gf_pow, gf_eval)


def sqrt_polypart(q, x):
    """Polynomial part s of sqrt(q) at x = oo (deg q even, lc a square)."""
    d = sp.degree(q, x)
    assert d % 2 == 0
    t = sp.Dummy('t')
    qt = sp.expand(q.subs(x, 1 / t) * t ** d)
    ser = sp.sqrt(qt).series(t, 0, d // 2 + 1).removeO()
    return sp.expand(sp.expand(ser).subs(t, 1 / x) * x ** (d // 2))


def fundamental_unit(q, x, maxsteps=60):
    """A unit A + B*y of Q[x][y]/(y^2 - q), found from the continued
    fraction of sqrt(q).  Returns (A, B, c) with A^2 - q*B^2 = c in Q*,
    or None if no unit appears within maxsteps partial quotients."""
    s = sqrt_polypart(q, x)
    P, Q = sp.S(0), sp.S(1)
    hm2, hm1 = sp.S(0), sp.S(1)
    km2, km1 = sp.S(1), sp.S(0)
    for _ in range(maxsteps):
        a = sp.div(sp.expand(P + s), Q, x)[0]
        h = sp.expand(a * hm1 + hm2)
        k = sp.expand(a * km1 + km2)
        c = sp.expand(h ** 2 - q * k ** 2)
        if not c.has(x) and c != 0 and k != 0:
            lc = sp.LC(k, x)
            h, k = sp.expand(h / lc), sp.expand(k / lc)
            return h, k, sp.expand(c / lc ** 2)
        P = sp.expand(a * Q - P)
        Q = sp.cancel((q - P ** 2) / Q)
        bits = max((abs(co.p).bit_length() + abs(co.q).bit_length()
                    for co in sp.Poly(Q, x).coeffs()), default=0)
        if bits > 8000:                  # non-torsion signature: give up
            return None
        hm2, hm1, km2, km1 = hm1, h, km1, k
    return None


def pseudo_elliptic(N, q, x, vdeg=None, maxsteps=60):
    """int N/sqrt(q) dx by the parallel method, unit-logand branch:
    all residues vanish (sub-critical branch poles), so the logand is a
    unit of O (Remark 7.7); its coefficient gamma and the rational part
    V0 + V1*y are the unknowns of the linear system."""
    res = fundamental_unit(q, x, maxsteps)
    if res is None:
        return None
    A, B, c = res
    qp = sp.diff(q, x)
    # Du = A' + (B' + B q'/(2q)) y ;  Du/u = Du (A - B y)/c
    b1 = sp.cancel(sp.diff(B, x) + B * qp / (2 * q))
    r0 = sp.cancel((sp.diff(A, x) * A - b1 * B * q) / c)
    r1 = sp.cancel((b1 * A - sp.diff(A, x) * B) / c)
    # ansatz  gamma*(r0 + r1 y) + D(V0 + V1 y) = (0 + (N/q) y)
    g = sp.Symbol('gamma')
    if vdeg is None:
        vdeg = sp.degree(N, x) + 2
    v0 = sp.symbols('v0_:%d' % (vdeg + 1))
    v1 = sp.symbols('v1_:%d' % (vdeg + 1))
    V0 = sp.Add(*[ci * x ** i for i, ci in enumerate(v0)])
    V1 = sp.Add(*[ci * x ** i for i, ci in enumerate(v1)])
    e0 = sp.cancel(g * r0 + sp.diff(V0, x))
    e1 = sp.cancel(g * r1 + sp.diff(V1, x) + V1 * qp / (2 * q) - N / q)
    eqs = []
    for e in (e0, e1):
        eqs += sp.Poly(sp.fraction(sp.cancel(e))[0], x).coeffs()
    unks = [g] + list(v0) + list(v1)
    sol = sp.linsolve(eqs, unks)
    if not sol:
        return None
    sub = dict(zip(unks, list(sol)[0]))
    frees = set().union(*[sp.sympify(v).free_symbols
                          for v in sub.values()]) & set(unks)
    sub = {kk: sp.sympify(v).subs({f: 0 for f in frees})
           for kk, v in sub.items()}
    # exact componentwise verification
    assert sp.cancel(e0.subs(sub)) == 0 and sp.cancel(e1.subs(sub)) == 0
    y = sp.sqrt(q)
    return (sub[g] * sp.log(sp.expand(A) + sp.expand(B) * y)
            + V0.subs(sub) + V1.subs(sub) * y)


# ---------------------------------------------------------------- mod p
def _polypart_sqrt_modp(q, x, p):
    """Polynomial part s of sqrt(q) in GF(p)[x]((1/x)), q of even degree
    with a square leading coefficient mod p; None if no square root."""
    Q = sp.Poly(q, x, modulus=p)
    d2 = Q.degree()
    if d2 % 2:
        return None
    d = d2 // 2
    lc = int(Q.LC()) % p
    r = next((r for r in range(p) if (r * r - lc) % p == 0), None)
    if r is None:
        return None
    coeffs = [0] * (d + 1)               # coeffs[k] = coefficient of x^(d-k)
    coeffs[0] = r
    qc = {d2 - k: int(Q.coeff_monomial(x ** (d2 - k))) % p for k in range(d2 + 1)}
    inv2r = pow(2 * r, -1, p)
    for k in range(1, d + 1):
        acc = sum(coeffs[i] * coeffs[k - i] for i in range(1, k)) % p
        coeffs[k] = ((qc.get(d2 - k, 0) - acc) * inv2r) % p
    return sp.Poly(sum(coeffs[k] * x ** (d - k) for k in range(d + 1)), x, modulus=p)


def unit_degree_modp(q, x, p, maxsteps=10000):
    """Order of the class [oo+ - oo-] on the reduction of y^2 = q modulo a
    good prime p: the degree of the fundamental unit of GF(p)[x][y], found
    from the (periodic) continued fraction of sqrt(q) over GF(p)."""
    s = _polypart_sqrt_modp(q, x, p)
    if s is None:
        return None
    Qp = sp.Poly(q, x, modulus=p)
    P, Q = sp.Poly(0, x, modulus=p), sp.Poly(1, x, modulus=p)
    hm2, hm1 = sp.Poly(0, x, modulus=p), sp.Poly(1, x, modulus=p)
    km2, km1 = sp.Poly(1, x, modulus=p), sp.Poly(0, x, modulus=p)
    for _ in range(maxsteps):
        a = (P + s).quo(Q)
        h, k = a * hm1 + hm2, a * km1 + km2
        c = h ** 2 - Qp * k ** 2
        if c.degree() <= 0 and not c.is_zero and not k.is_zero:
            return h.degree()
        P = a * Q - P
        Q = (Qp - P ** 2).quo(Q)
        hm2, hm1, km2, km1 = hm1, h, km1, k
    return None


def nontorsion_certificate(q, x, nprimes=4, pmax=1000):
    """Certify that [oo+ - oo-] is NOT torsion on y^2 = q (q in Q[x], even
    degree) by reduction modulo primes of good reduction: if the class had
    order N, its reduction modulo a good prime p would have order N_p with
    N = N_p * p^a, a >= 0 (reduction is injective on prime-to-p torsion);
    two primes whose N_p are incompatible with any common N certify
    non-torsion.  Returns (certified, [(p, N_p), ...])."""
    Qx = sp.Poly(q, x)
    lc = Qx.LC()
    disc = sp.discriminant(Qx)
    bad = sp.Integer(2) * sp.fraction(sp.nsimplify(lc))[0] * sp.fraction(sp.nsimplify(lc))[1]
    for c in Qx.all_coeffs():
        bad *= sp.fraction(sp.nsimplify(c))[1]
    bad *= sp.fraction(sp.nsimplify(disc))[0] or 1
    data = []
    for p in sp.primerange(3, pmax):
        if bad % p == 0:
            continue
        Np = unit_degree_modp(q, x, p)
        if Np is None:
            continue                      # oo+- not rational mod p
        data.append((p, Np))
        if len(data) >= nprimes:
            break
    return _incompatible(data), data


def _incompatible(data):
    """No finite N has N = N_p p^a for every (p, N_p) in data: for two primes
    N_{p1}/N_{p2} = p2^b/p1^a, so in lowest terms the numerator must be a
    power of p2 (or 1) and the denominator a power of p1 (or 1)."""
    for i in range(len(data)):
        for j in range(i + 1, len(data)):
            (p1, n1), (p2, n2) = data[i], data[j]
            r = sp.Rational(n1, n2)
            ok_num = r.p == 1 or sp.factorint(r.p).keys() == {p2}
            ok_den = r.q == 1 or sp.factorint(r.q).keys() == {p1}
            if not (ok_num and ok_den):
                return True
    return False


# --------------------------------------------- Jacobian arithmetic mod p
# Cantor's algorithm on y^2 = f, deg f = 2g + 1 (one place at infinity), over
# GF(p): divisor classes as reduced Mumford pairs (u, v), u monic of degree
# <= g, v^2 = f mod u, as galoistools coefficient lists (highest degree
# first); the identity is ([1], []).  Used by nontorsion_divisor_certificate
# (Proposition 9.4 for a residue divisor supported at finite places).

_JZERO = ([1], [])


def cantor_add(f, D1, D2, p):
    """The reduced Mumford representative of the class of D1 + D2."""
    u1, v1 = D1
    u2, v2 = D2
    e1, e2, d1 = gf_gcdex(u1, u2, p, ZZ)                    # d1 = e1 u1 + e2 u2
    c1, c2, d = gf_gcdex(d1, gf_add(v1, v2, p, ZZ), p, ZZ)  # d = c1 d1 + c2 (v1 + v2)
    s1, s2 = gf_mul(c1, e1, p, ZZ), gf_mul(c1, e2, p, ZZ)
    u = gf_quo(gf_mul(u1, u2, p, ZZ), gf_mul(d, d, p, ZZ), p, ZZ)
    t = gf_add(gf_add(gf_mul(gf_mul(s1, u1, p, ZZ), v2, p, ZZ),
                      gf_mul(gf_mul(s2, u2, p, ZZ), v1, p, ZZ), p, ZZ),
               gf_mul(c2, gf_add(gf_mul(v1, v2, p, ZZ), f, p, ZZ), p, ZZ), p, ZZ)
    v = gf_rem(gf_quo(t, d, p, ZZ), u, p, ZZ)
    g = (gf_degree(f) - 1) // 2
    while gf_degree(u) > g:
        u = gf_monic(gf_quo(gf_sub(f, gf_mul(v, v, p, ZZ), p, ZZ), u, p, ZZ), p, ZZ)[1]
        v = gf_rem(gf_neg(v, p, ZZ), u, p, ZZ)
    return gf_monic(u, p, ZZ)[1], gf_strip(v)


def cantor_mul(f, n, D, p):
    """[n] D by double-and-add, n >= 0."""
    R, Q = _JZERO, D
    while n:
        if n & 1:
            R = cantor_add(f, R, Q, p)
        Q = cantor_add(f, Q, Q, p)
        n >>= 1
    return R


def divisor_order_modp(f, points, p):
    """The order of the class of sum_P n_P (P - oo) in the Jacobian of y^2 = f
    over GF(p), points = [((x0, y0), n_P)]: the Mumford representative of the
    divisor by Cantor's algorithm, a multiple M of the order by baby-step
    giant-step in the Weil interval [(sqrt p - 1)^2g, (sqrt p + 1)^2g] (which
    contains #J(GF(p))), and the least divisor of M annihilating the class."""
    D = _JZERO
    for (x0, y0), n in points:
        P = ([1, (-x0) % p], gf_strip([(y0 if n > 0 else -y0) % p]))
        for _ in range(abs(n)):
            D = cantor_add(f, D, P, p)
    if D == _JZERO:
        return 1
    g = (gf_degree(f) - 1) // 2
    lo = max(1, math.floor((math.sqrt(p) - 1) ** (2 * g)))
    hi = math.ceil((math.sqrt(p) + 1) ** (2 * g))
    m = math.isqrt(hi - lo) + 1
    key = lambda E: (tuple(E[0]), tuple(E[1]))
    baby, B = {}, _JZERO
    for j in range(m):
        baby.setdefault(key(B), j)
        B = cantor_add(f, B, D, p)
    G, step, M = cantor_mul(f, lo, D, p), cantor_mul(f, m, D, p), None
    for i in range(m + 1):
        j = baby.get(key(G))
        if j is not None and lo + i * m - j > 0:
            M = lo + i * m - j                  # [lo + i m] D = [j] D
            break
        G = cantor_add(f, G, step, p)
    if M is None:
        return None
    for d in sp.divisors(M):
        if cantor_mul(f, d, D, p) == _JZERO:
            return d


def odd_model(q, r, p):
    """For q (coefficients over GF(p), highest first) of even degree d with a
    root r: the odd-degree model w^2 = f(v) of y^2 = q, f(v) = v^d q(r + 1/v)
    of degree d - 1 (the coefficient of v^d is q(r) = 0), and the point map
    (x0, y0) -> (1/(x0 - r), y0/(x0 - r)^(d/2))."""
    d = len(q) - 1
    f = []
    for i, c in enumerate(reversed(q)):        # q_i (r v + 1)^i v^(d - i)
        if c % p:
            f = gf_add(f, gf_mul([c % p], gf_pow([r % p, 1], i, p, ZZ), p, ZZ) + [0] * (d - i), p, ZZ)

    def pt(x0, y0):
        s = pow((x0 - r) % p, -1, p)
        return s, y0 * pow(s, d // 2, p) % p
    return gf_strip(f), pt


def nontorsion_divisor_certificate(q, x, places, minpoly=None, nprimes=2, pmax=1000, budget=2 * 10 ** 7):
    """Certify that the class of a degree-0 divisor sum n_P P on y^2 = q
    (q in Q[x]) with places P = (x0, y0) of constant coordinates is NOT
    torsion, by reduction modulo primes of good reduction (Proposition 9.4
    for the residue divisor that Algorithm 3(d) leaves unrealised): if the
    class had finite order N, its reduction at a degree-one prime above p of
    the number field K = Q(theta) of the coordinates would have order N_p
    with N = N_p p^a, a >= 0 (reduction is injective on the prime-to-p
    torsion), so two primes with incompatible N_p exclude every finite
    order.  N_p is the order of the reduced class in the Jacobian over GF(p)
    (divisor_order_modp), on an odd-degree model when deg q is even (a root
    of q mod p moved to infinity; primes without one are skipped); primes
    whose Weil bound exceeds budget are skipped.  places is [((a, b), n)]
    with a, b the coordinates of x0, y0 over Q on the power basis of theta
    (lowest first) and minpoly the minimal polynomial of theta as a
    coefficient list (None for K = Q).  Returns (certified, [(p, N_p), ...])."""
    Qx = sp.Poly(q, x)
    d = Qx.degree()
    two_g = d - 1 if d % 2 else d - 2
    qc = [sp.Rational(c) for c in Qx.all_coeffs()]
    mu = [sp.Rational(c) for c in (minpoly if minpoly is not None else [1, 0])]
    bad = sp.Integer(2)
    for c in (qc + mu + [sp.discriminant(Qx), sp.discriminant(sp.Poly(mu, sp.Dummy()))]
              + [c for (a, b), _ in places for c in a + b]):
        c = sp.Rational(c)
        bad *= (c.p or 1) * c.q
    data = []
    for p in sp.primerange(3, pmax):
        if bad % p == 0 or (math.sqrt(p) + 1) ** two_g > budget:
            continue
        red = lambda c: c.p * pow(c.q, -1, p) % p
        thetas = [t for t in range(p) if gf_eval([red(c) for c in mu], t, p, ZZ) == 0]
        if not thetas:
            continue                         # no degree-one prime of K above p
        th = thetas[0]
        ev = lambda a: sum(red(sp.Rational(c)) * pow(th, i, p) for i, c in enumerate(a)) % p
        pts = [((ev(a), ev(b)), n) for (a, b), n in places]
        f = [red(c) for c in qc]
        if d % 2 == 0:
            roots = [r for r in range(p)
                     if gf_eval(f, r, p, ZZ) == 0 and all(r != x0 for (x0, _), _ in pts)]
            if not roots:
                continue
            f, mp = odd_model(f, roots[0], p)
            pts = [(mp(x0, y0), n) for (x0, y0), n in pts]
        if any((y0 * y0 - gf_eval(f, x0, p, ZZ)) % p for (x0, y0), _ in pts):
            continue
        Np = divisor_order_modp(f, pts, p)
        if Np is None:
            continue
        data.append((p, Np))
        if _incompatible(data):
            return True, data
        if len(data) >= nprimes:
            break
    return False, data
