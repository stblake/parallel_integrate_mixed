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

import sympy as sp


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
    for i in range(len(data)):
        for j in range(i + 1, len(data)):
            (p1, n1), (p2, n2) = data[i], data[j]
            r = sp.Rational(n1, n2)
            num, den = r.p, r.q            # need num = p1^a (or 1), den = p2^b (or 1)
            ok_num = num == 1 or (sp.factorint(num).keys() == {p1})
            ok_den = den == 1 or (sp.factorint(den).keys() == {p2})
            if not (ok_num and ok_den):
                return True, data
    return False, data
