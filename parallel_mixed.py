"""parallel_mixed.py -- the merged pipeline (milestone (i)).

One generic ParallelIntegrateMixed covering both previous slices:
m = 1 (no radical: parallel_flat) and m = 2 with q squarefree over
R = Q[g_1,...,g_k] (radical anywhere in the tower: the derivatives
D g_i are elements and may involve y).  Elements are coordinate pairs
(c0, c1) <-> c0 + c1*y on the Trager basis (1, y), c_i in Q(g_1..g_k).

Pipeline (paper section numbers):
  classification of every denominator prime by Definition 4.4 computed
  generically -- eta_P on the generators and Dy (Lemma 4.3), uniformiser
  p (unramified) or y (branch), delta_P = 1 + eta_P (Theorem 4.6);
  Hermite exponents and the special guess (Corollary 5.9); residues
  tau_P = e*(f h/Dh)|_P (Theorem 7.5) with curve splitting: linear
  primes split by sqrt(q mod p), quadratic primes split by y when
  disc = s^2 q (the norm identity N(2a g + b -+ s y) = 4a p realises
  the logands, Lemma 7.2); the constancy test; unit candidates from
  pell (Remark 7.7); the pair-valued ansatz, linsolve, exact
  componentwise verification.

Reported, not computed: realisation of unequal split residues at
linear primes (torsion / norm search: Parts I--II, milestone iii);
critical branch residues; residues at primes of degree > 2 in every
generator; m >= 3 (which, by Lemma 3.4, so far arises only in
flattenable examples).
"""

import sympy as sp

def _c(e):
    try:
        return sp.cancel(e, extension=True)
    except Exception:
        return sp.cancel(e)
from itertools import product as _iproduct
from pell import fundamental_unit, nontorsion_certificate
try:                      # shared codebase with Parts I and III
    from weier import division_poly_order
    from rnrad2 import RadicalField, exact_degree_bounds
    import rnrad2 as _rn
    _HAVE_RN = True
except Exception:         # pragma: no cover
    _HAVE_RN = False

# ---------------------------------------------------------------- pairs

def _padd(u, v):  return (_c(u[0] + v[0]), _c(u[1] + v[1]))
def _pscale(a, u): return (_c(a * u[0]), _c(a * u[1]))
def _pmul(u, v, q):
    return (_c(u[0] * v[0] + u[1] * v[1] * q),
            _c(u[0] * v[1] + u[1] * v[0]))
def _pdiv(u, v, q):
    N = _c(v[0] ** 2 - q * v[1] ** 2)
    w = _pmul(u, (v[0], -v[1]), q)
    return (_c(w[0] / N), _c(w[1] / N))

class Tower:
    """gens with derivative pairs; q = None means m = 1."""
    def __init__(self, gens, derivs, q=None):
        self.gens, self.q = list(gens), q
        self.derivs = [(sp.cancel(d[0]), sp.cancel(d[1])) for d in derivs]
        if q is not None:
            Q = self._Dhat(q)
            self.Dy = (sp.cancel(Q[1] / 2), sp.cancel(Q[0] / (2 * q)))
    def _Dhat(self, c):
        out = (sp.S(0), sp.S(0))
        for g, d in zip(self.gens, self.derivs):
            out = _padd(out, _pscale(sp.diff(c, g), d))
        return out
    def D(self, u):
        out = self._Dhat(u[0])
        if self.q is None:
            return out
        h1 = self._Dhat(u[1])
        out = _padd(out, _pmul(h1, (sp.S(0), sp.S(1)), self.q))
        return _padd(out, _pscale(u[1], self.Dy))

# ------------------------------------------------------------ valuations

def _vp(expr, p, gens):
    expr = sp.cancel(expr)
    if expr == 0:
        return sp.oo
    n, d = sp.fraction(expr)
    def mult(poly):
        m, P, Q = 0, sp.Poly(poly, *gens), sp.Poly(p, *gens)
        while True:
            qq, r = sp.div(P, Q)
            if not r.is_zero:
                return m
            m, P = m + 1, qq
    return mult(n) - mult(d)

def _vP(u, p, T, branch):
    g = T.gens
    if T.q is None or not branch:
        return min(_vp(u[0], p, g), _vp(u[1], p, g) + (0 if T.q else sp.oo)) \
               if T.q else _vp(u[0], p, g)
    return min(2 * _vp(u[0], p, g), 2 * _vp(u[1], p, g) + 1)

def _eta(T, p, branch):
    vals = [-_vP(d, p, T, branch) for d in T.derivs]
    if T.q is not None:
        vals.append(-_vP(T.Dy, p, T, branch))
    return max([0] + [v for v in vals if v is not sp.oo and v != -sp.oo])

def _classify(T, p):
    """(branch?, eta, delta, special?) at the prime(s) over p."""
    branch = T.q is not None and _vp(T.q, p, T.gens) > 0
    eta = _eta(T, p, branch)
    pi = (sp.S(0), sp.S(1)) if branch else (p, sp.S(0))   # y or p
    special = eta + _vP(T.D(pi), p, T, branch) >= 1
    return branch, eta, 1 + eta, special

# -------------------------------------------------------------- residues

def _points_over(T, p):
    """Places over p as substitutions [(gen, root, yval)], via a generator
    in which p has degree <= 2; yval is None for m = 1."""
    for g in T.gens:
        P = sp.Poly(p, g)
        if P.degree() in (1, 2, 3, 4) and all(
                c.free_symbols.isdisjoint({g}) for c in P.all_coeffs()):
            cc = [t.as_expr() if hasattr(t, 'as_expr') else sp.sympify(t)
                  for t in P.all_coeffs()]
            if P.degree() == 1:
                roots = [sp.cancel(-cc[1] / cc[0])]
            elif P.degree() in (3, 4):
                if any(sp.sympify(z).free_symbols for z in cc):
                    continue
                rd = sp.roots(P)
                if sum(rd.values()) != P.degree():
                    continue
                roots = [sp.radsimp(r) for r, m in rd.items() for _ in range(m)]
            else:
                dsc = sp.sqrt(sp.factor(cc[1] ** 2 - 4 * cc[0] * cc[2]))
                roots = [sp.cancel((-cc[1] + sg * dsc) / (2 * cc[0]))
                         for sg in (1, -1)]
            pts = []
            for rho in roots:
                if T.q is None:
                    pts.append((g, rho, None))
                    continue
                qbar = sp.cancel(T.q.subs(g, rho))
                r = sp.sqrt(sp.factor(qbar))
                if sp.simplify(r ** 2 - qbar) == 0 and not r.has(sp.I):
                    pass
                for eps in (1, -1):
                    pts.append((g, rho, eps * r))
            return pts
    return None

def _iszero(v):
    """Zero test that handles algebraic constants such as sqrt(-I), which
    simplify alone does not canonicalise; symbolic expressions fall back
    to simplify."""
    v = sp.sympify(v)
    if v.free_symbols:
        return sp.simplify(v) == 0
    return sp.simplify(sp.expand_complex(v)) == 0


def _reduce_at(expr, pt, y_symbol):
    g, rho, yv = pt
    e = expr
    if yv is not None:
        e = e.subs(y_symbol, yv)
    return sp.simplify(sp.cancel(e).subs(g, rho))

def _resfmt(v):
    return sp.nsimplify(sp.simplify(v))


def _norm_search(q, p, g, kmax=2, dbmax=2):
    """First solution of _norm_search_all (kept for callers that want one)."""
    for sol in _norm_search_all(q, p, g, kmax, dbmax):
        return sol
    return None


def _norm_search_all(q, p, g, kmax=2, dbmax=2):
    """Yield every u = a + b*y with a^2 - q b^2 = c * p^k of small degree
    (b normalised monic).  Different solutions vanish on different subsets
    of the places over p, so the realisation must try them all."""
    dq, dp = sp.degree(q, g), sp.degree(p, g)
    for k in range(1, kmax + 1):
        for db in range(0, dbmax + 1):
            da = (max(dq + 2 * db, k * dp) + 1) // 2
            ac = sp.symbols('na0:%d' % (da + 1))
            bc = sp.symbols('nb0:%d' % db) if db else ()
            c = sp.Symbol('nc')
            a = sp.Add(*[ci * g ** i for i, ci in enumerate(ac)])
            b = sp.Add(*[ci * g ** i for i, ci in enumerate(bc)]) + g ** db
            eq = sp.expand(a ** 2 - q * b ** 2 - c * p ** k)
            sols = sp.solve(sp.Poly(eq, g).coeffs(), list(ac) + list(bc) + [c],
                            dict=True)
            for s in sols:
                aa, bb, cc = a.subs(s), b.subs(s), s.get(c, c)
                if cc != 0 and aa.free_symbols <= {g} and cc.free_symbols == set():
                    yield sp.expand(aa), sp.expand(bb), cc, k



def _vanish_order(T, u, pt, Y):
    """Order of vanishing of u0 + u1*y at a place with constant
    coordinates (series in the base generator)."""
    g, rho, yv = pt
    if sp.sympify(rho).free_symbols or not T.q.free_symbols <= {g}:
        return 1
    e = sp.Dummy('e')
    r = sp.sqrt(T.q.subs(g, rho))
    eps = 1 if _iszero(yv - r) else (-1 if _iszero(yv + r) else None)
    if eps is None:
        return 1
    ub = (u[0] + u[1] * eps * sp.sqrt(T.q.subs(g, rho + e))).subs(g, rho + e)
    ser = sp.series(sp.expand(ub), e, 0, 8).removeO()
    k = 0
    while k < 8 and _iszero(ser.coeff(e, k)):
        k += 1
    return k

def _realise_points(T, p, pts, taus, Y, verbose=False):
    """Corollary 7.6 at the places over p: return [(tau, u_pair)] or None."""
    if all(tt == taus[0] for tt in taus):
        return [(taus[0], (p, sp.S(0)))] if taus[0] != 0 else []
    g = pts[0][0]
    for a, b, c, k in _norm_search_all(T.q, p, g):
        out, ok = [], True
        for sg in (1, -1):
            uu = (a, sg * b)
            hits = [(pt, tt) for pt, tt in zip(pts, taus)
                    if _iszero(_reduce_at(uu[0] + uu[1] * Y, pt, Y))]
            gammas = [sp.nsimplify(tt / _vanish_order(T, uu, pt, Y), [sp.sqrt(3)])
                      for pt, tt in hits]
            if not (gammas and all(sp.simplify(gg - gammas[0]) == 0 for gg in gammas)):
                ok = False
                break
            if gammas[0] != 0:
                out.append((gammas[0], uu))
        if ok:
            if verbose:
                for gm, uu in out:
                    print(f"      norm factor {uu[0]} + ({uu[1]})*y "
                          f"(N = {c}*({p})**{k}): coefficient {gm}")
            return out
    return _torsion_realise(T, p, pts, taus, Y, verbose=verbose)



def _certify_nonconstant(tau, gens):
    """Exact decision of whether a residue tau -- an element of kappa(P)
    given as an expression in the generators, algebraic numbers and at
    most one algebraic function sqrt(A) -- lies outside Fbar.
    True: certified non-constant.  False: constant.  None: undecided."""
    G = set(gens)
    tau = sp.together(sp.sympify(tau))
    if tau.free_symbols.isdisjoint(G):
        return False
    pows = [a for a in tau.atoms(sp.Pow) if not a.base.free_symbols.isdisjoint(G)]
    if any((not a.exp.is_Rational) or a.exp.q not in (1, 2) for a in pows):
        return None
    algs = {a.base for a in pows if a.exp.q == 2}
    if not algs:
        n, d = sp.fraction(_c(tau))
        return any(not sp.sympify(z).free_symbols.isdisjoint(G) for z in (n, d))
    if len(algs) != 1:
        return None
    A = algs.pop()
    S = sp.Dummy('S')
    e = tau.subs(sp.sqrt(A), S)
    n, d = sp.fraction(sp.together(e))
    PS = sp.Poly(S ** 2 - A, S)
    red = lambda z: sp.rem(sp.Poly(sp.expand(z), S), PS).as_expr()
    n, d = red(n), red(d)
    dbar = d.subs(S, -S)
    N, D0 = red(sp.expand(n * dbar)), red(sp.expand(d * dbar))
    if S in D0.free_symbols:
        return None
    a, b = N.subs(S, 0), sp.expand(N).coeff(S, 1)
    r = sp.sqrt(sp.factor(A))
    is_sq = not any(isinstance(p, sp.Pow) and p.exp.is_Rational and p.exp.q == 2
                    and not p.base.free_symbols.isdisjoint(G) for p in r.atoms(sp.Pow))
    if is_sq:
        return _certify_nonconstant(sp.cancel((a + b * r) / D0), gens)
    if _c(b / D0) != 0:
        return True
    return _certify_nonconstant(sp.cancel(a / D0), gens)


def _residue_free(T, g, Y):
    """n = 1, D = d/dx: certify that g dx (g a pair) has zero residue at
    every affine place, by classical series at unramified and branch
    places.  A False here means the realisation is not trusted."""
    x = T.gens[0]
    q = T.q
    den = sp.lcm(sp.fraction(_c(g[0]))[1], sp.fraction(_c(g[1]))[1])
    e = sp.Dummy('e')
    for P_, _ in sp.factor_list(sp.Poly(den, x))[1]:
        p = P_.as_expr()
        if not p.has(x):
            continue
        # sub-critical poles carry no residue (Theorem 7.4(ii)); n = 1 with
        # D = d/dx has delta = 1 at unramified and delta = e_P = 2 at branch
        # primes, so only v_P(g) <= -delta_P needs an evaluation
        branch = sp.gcd(sp.Poly(p, x), sp.Poly(q, x)).degree() > 0
        if _vP(g, p, T, branch) > -(2 if branch else 1):
            continue
        rd = sp.roots(sp.Poly(p, x))
        if sum(rd.values()) != sp.degree(p, x):
            return False
        for rho in rd:
            if sp.simplify(q.subs(x, rho)) != 0:
                yser = sp.sqrt(q.subs(x, rho + e))
                for sg in (1, -1):
                    loc = g[0].subs(x, rho + e) + sg * g[1].subs(x, rho + e) * yser
                    res = sp.series(loc, e, 0, 1).removeO().coeff(e, -1)
                    if sp.simplify(res) != 0:
                        return False
            else:
                x_loc = rho + e ** 2
                yloc = e * sp.sqrt(sp.cancel(q.subs(x, x_loc) / e ** 2))
                loc = 2 * e * (g[0].subs(x, x_loc) + g[1].subs(x, x_loc) * yloc)
                res = sp.series(loc, e, 0, 1).removeO().coeff(e, -1)
                if sp.simplify(res) != 0:
                    return False
    return True


def _vinfty_residue(T, f, Y):
    """Hypertangent top generator t, Dt = eta (1 + t^2): the place v_oo has
    delta = 1 and uniformiser 1/t; for v_oo(f) = -1 the residue is
    tau = -(lim f/t)/eta in kappa(v_oo) = K_{n-1}(y), returned as a pair.
    None if the top generator is not hypertangent or v_oo(f) != -1."""
    t = T.gens[-1]
    a, b = T.derivs[-1]
    ea, eb = sp.cancel(a / (1 + t ** 2)), sp.cancel(b / (1 + t ** 2))
    if ea.has(t) or eb.has(t) or (ea == 0 and eb == 0):
        return None
    def vinf(c):
        c = sp.cancel(c)
        if c == 0:
            return None
        n, d = sp.fraction(c)
        return sp.degree(d, t) - sp.degree(n, t)
    vs = [v for v in (vinf(f[0]), vinf(f[1])) if v is not None]
    if not vs or min(vs) != -1:
        return None
    def lead(c):
        c = sp.cancel(c)
        if c == 0 or vinf(c) != -1:
            return sp.S(0)
        n, d = sp.fraction(c)
        return sp.cancel(sp.LC(n, t) / sp.LC(d, t))
    cpair = (lead(f[0]), lead(f[1]))
    tau = _pdiv(cpair, (ea, eb), T.q)
    return (_c(-tau[0]), _c(-tau[1]))

def _deep_residues(T, f, p, pts, Y):
    """Laurent residues at a delta = 1 normal prime with a pole of order
    >= 2 (well-defined: exact parts contribute none).  Single-generator
    slice: requires gens = [g] with Dg = 1."""
    g = T.gens[0]
    e = sp.Dummy('e')
    out = []
    for (gv, rho, yval) in pts:
        r = sp.sqrt(sp.factor(T.q.subs(g, rho)))
        eps = sp.simplify(sp.cancel(yval / r))
        yser = eps * sp.sqrt(T.q.subs(g, rho + e))
        floc = f[0].subs(g, rho + e) + f[1].subs(g, rho + e) * yser
        ser = sp.series(floc, e, 0, 1).removeO()
        out.append(_resfmt(ser.coeff(e, -1)))
    return out



def _algzero(e):
    z = sp.simplify(e)
    if z == 0:
        return True
    if z.free_symbols:
        return False
    try:
        return abs(complex(sp.N(z, 30))) < 1e-20
    except (TypeError, ValueError):
        return sp.simplify(sp.radsimp(z)) == 0


def _ell_ops(q, g):
    """Chord-and-tangent group law on y^2 = q(g), deg q = 3, after
    normalising to a monic cubic (X = c3*g, Ytil = c3*y)."""
    c = sp.Poly(q, g).all_coeffs()          # [c3, c2, c1, c0]
    c3 = c[0]
    # monic model: Ytil^2 = X^3 + c[1]*X^2 + c[2]*c3*X + c[3]*c3**2
    def to_m(P):  return (sp.radsimp(c3 * P[0]), sp.radsimp(c3 * P[1]))
    def add(P, Q):
        if P is None: return Q
        if Q is None: return P
        x1, y1 = P; x2, y2 = Q
        if _algzero(x1 - x2):
            if _algzero(y1 + y2): return None
            lam = sp.radsimp((3 * x1 ** 2 + 2 * c[1] * x1 + c[2] * c3) / (2 * y1))
        else:
            lam = sp.radsimp((y2 - y1) / (x2 - x1))
        x3 = sp.radsimp(lam ** 2 - c[1] - x1 - x2)
        return (x3, sp.radsimp(lam * (x1 - x3) - y1))
    return to_m, add


def _torsion_realise(T, p, pts, taus, Y, bound=24, verbose=False):
    """div realisation by torsion on an elliptic curve with one place at
    infinity (deg q = 3): order search for [P - oo] and additive Miller
    functions with div = m P - m oo.  Returns [(coeff, pair)] or None."""
    g = pts[0][0]
    q = T.q
    if sp.degree(q, g) != 3 or not q.free_symbols <= {g}:
        return None
    if any(sp.sympify(rho).free_symbols or sp.sympify(yv).free_symbols
           for _, rho, yv in pts):
        return None
    to_m, add = _ell_ops(q, g)
    c3 = sp.Poly(q, g).all_coeffs()[0]
    X0, Y0 = c3 * g, None                    # monic-model coordinates of (g, y)
    out = []
    for (gv, rho, yv), tau in zip(pts, taus):
        if tau == 0:
            continue
        P = to_m((rho, yv))
        # order: division-polynomial certificate when the model is depressed
        cc = sp.Poly(q, g).all_coeffs()
        m = None
        if _HAVE_RN and cc[1] == 0:
            m = division_poly_order(cc[2] * c3, cc[3] * c3 ** 2, P[0], P[1],
                                    Nmax=bound)
            if verbose and m is not None:
                print(f"      (order {m} certified by the division polynomial "
                      f"psi_{m})")
        if m is None:                       # fallback: repeated addition
            kP = P
            for k in range(2, bound + 1):
                kP = add(kP, P)
                if kP is None:
                    m = k
                    break
        if m is None:
            return None
        # additive Miller loop: f_{k+1} = f_k * line(kP, P) / vert((k+1)P)
        f_num, f_den = sp.S(1), sp.S(1)
        kP = P
        for k in range(1, m):
            x1, y1 = kP
            if _algzero(x1 - P[0]) and _algzero(y1 - P[1]):
                lam = sp.radsimp((3 * x1 ** 2
                                  + 2 * sp.Poly(q, g).all_coeffs()[1] * x1
                                  + sp.Poly(q, g).all_coeffs()[2] * c3) / (2 * y1))
            elif _algzero(x1 - P[0]):
                f_num *= (X0 - x1); kP = add(kP, P); continue
            else:
                lam = sp.radsimp((P[1] - y1) / (P[0] - x1))
            line = c3 * Y - y1 - lam * (X0 - x1)     # Ytil - y1 - lam (X - x1)
            kP = add(kP, P)
            f_num *= line
            if kP is not None:
                f_den *= (X0 - kP[0])
        # reduce modulo Y^2 = q and record with coefficient tau/m
        num = sp.rem(sp.Poly(sp.expand(f_num), Y), sp.Poly(Y ** 2 - q, Y)).as_expr()
        u0 = sp.cancel(sp.radsimp((num + num.subs(Y, -Y)) / 2) / f_den)
        u1 = sp.cancel(sp.radsimp((num - num.subs(Y, -Y)) / (2 * Y)) / f_den)
        out.append((sp.nsimplify(tau / m, [sp.sqrt(3)]), (u0, u1)))
        if verbose:
            print(f"      torsion: [P - oo] of order {m} at ({rho}, {yv}); "
                  f"Miller logand with coefficient {sp.nsimplify(tau/m, [sp.sqrt(3)])}")
    return out


# ------------------------------------------------------------- pipeline

def parallel_integrate_mixed(f, T, bounds=None, extension=None, verbose=False,
                             split_specials=False):
    """f = (f0, f1) <-> f0 + f1*y.  Returns a sympy expression, or a
    status tuple ('not elementary', ...) / ('needs torsion realisation',
    ...) / ('failed', ...)."""
    gens, q = T.gens, T.q
    bounds_given = bounds
    Y = sp.Dummy('y')
    # the integrand must be a rational function of the generators: an opaque
    # function such as atan(x) would be treated as a constant by the linear
    # solver and produce a wrong integral
    for comp in (f[0], f[1] if q is not None else sp.S(0)):
        cc = sp.cancel(sp.sympify(comp))
        n_, d_ = sp.fraction(cc)
        bad = (not n_.is_polynomial(*gens) or not d_.is_polynomial(*gens)
               or any(not a.free_symbols.isdisjoint(set(gens))
                      for a in cc.atoms(sp.Function)))
        if bad:
            raise ValueError(f"integrand component {comp} is not a rational "
                             "function of the generators; build the tower first")
    f = (sp.cancel(f[0]), sp.cancel(f[1] if q is not None else 0))
    d = sp.lcm(sp.fraction(f[0])[1], sp.fraction(f[1])[1])
    det_logs, unk_logs, denv, torsion = [], [], sp.S(1), []

    fl = (sp.factor_list(d, extension=extension)[1] if extension is not None
          else sp.factor_list(sp.Poly(d, *gens))[1])
    for P_, mult in fl:
        p = P_ if not hasattr(P_, 'as_expr') else P_.as_expr()
        if not any(p.has(g) for g in gens):
            continue
        branch, eta, delta, special = _classify(T, p)
        e_P = 2 if branch else 1
        vP = _vP(f, p, T, branch)
        if special:
            denv *= p ** mult
            unk_logs.append((p, sp.S(0)))
            if verbose:
                print(f"  ({p}): special; s-part {p}**{mult}, "
                      f"candidate log({p})")
            continue
        if verbose:
            print(f"  ({p}): {'branch' if branch else 'unramified'}, "
                  f"delta = {delta}, v_P(f) = {vP}"
                  + ("  [sub-critical]" if vP > -delta else ""))
        if vP < -delta:
            denv *= p ** sp.ceiling(sp.Rational(-vP - delta, e_P))
            if (delta == 1 and not branch and q is not None
                    and len(gens) == 1 and T.derivs[0] == (sp.S(1), sp.S(0))):
                pts = _points_over(T, p)
                if pts:
                    taus = _deep_residues(T, f, p, pts, Y)
                    if verbose:
                        print(f"      deep residues at order {-vP}: {taus}")
                    cert = [(_certify_nonconstant(tt, gens), tt) for tt in taus]
                    if any(cv is True for cv, _ in cert):
                        return ("not elementary", p,
                                [tt for cv, tt in cert if cv is True][0])
                    if any(cv is None for cv, _ in cert):
                        return ("failed", "residue constancy undecided", p,
                                [tt for cv, tt in cert if cv is None][0])
                    got = _realise_points(T, p, pts, taus, Y, verbose)
                    if got is None:
                        torsion.append((p, taus))
                    else:
                        det_logs.extend(got)
        if vP == -delta:
            # tau_P = e * (f h / Dh)|_P  with h = p
            Dp = T.D((p, sp.S(0)))
            tp = _pdiv(_pscale(e_P * p, f), Dp, q) if q is not None else \
                 (sp.cancel(e_P * p * f[0] / Dp[0]), sp.S(0))
            texpr = tp[0] + tp[1] * Y
            pts = _points_over(T, p)
            if pts is None:
                raise NotImplementedError(f"residues over ({p}): degree > 2 "
                                          "in every generator")
            if branch:
                raise NotImplementedError("critical branch residue")
            taus = [_resfmt(_reduce_at(texpr, pt, Y)) for pt in pts]
            if verbose:
                if q is None:
                    print(f"      residues {taus}")
                else:
                    print(f"      places {['y=%s' % str(pt[2]) for pt in pts]}: "
                          f"residues {taus}")
            cert = [(_certify_nonconstant(t, gens), t) for t in taus]
            if any(cv is True for cv, _ in cert):
                return ("not elementary", p, [t for cv, t in cert if cv is True][0])
            if any(cv is None for cv, _ in cert):
                return ("failed", "residue constancy undecided", p,
                        [t for cv, t in cert if cv is None][0])
            if all(t == taus[0] for t in taus):
                if taus[0] != 0:
                    det_logs.append((taus[0], (p, sp.S(0))))
                continue
            # quadratic y-split (disc = s^2 q => factors 2a*g + b -+ s*y,
            # norm identity N = 4a*p): try every generator direction
            done = False
            if q is not None:
                for gstar in gens:
                    P2 = sp.Poly(p, gstar)
                    if P2.degree() != 2:
                        continue
                    a, b, c = [tt.as_expr() if hasattr(tt, 'as_expr') else tt
                               for tt in P2.all_coeffs()]
                    if any(z.free_symbols & {gstar} for z in (a, b, c)) \
                       or not sp.sympify(a).is_rational:
                        continue
                    disc = sp.cancel(b ** 2 - 4 * a * c)
                    s2 = sp.cancel(disc / q)
                    s = sp.sqrt(sp.factor(s2))
                    if sp.simplify(s ** 2 - s2) != 0 or any(
                            isinstance(a_, sp.Pow) and a_.exp.is_Rational and not a_.exp.is_Integer
                            and not a_.base.free_symbols.isdisjoint(set(gens))
                            for a_ in s.atoms(sp.Pow)):
                        continue
                    ok, pend = True, []
                    for sg in (1, -1):
                        uu = (sp.expand(2 * a * gstar + b), -sg * s)
                        tv = [tt for pt, tt in zip(pts, taus)
                              if _iszero(_reduce_at(uu[0] + uu[1] * Y, pt, Y))]
                        if tv and all(tt == tv[0] for tt in tv):
                            pend.append((tv[0], uu))
                        else:
                            ok = False
                    if ok:
                        for tv0, uu in pend:
                            if tv0 != 0:
                                det_logs.append((tv0, uu))
                            if verbose:
                                print(f"      y-split factor {uu[0]} + "
                                      f"({uu[1]})*y: residue {tv0}")
                        done = True
                        break
            if done:
                continue
            got = _realise_points(T, p, pts, taus, Y, verbose)
            if got is not None:
                det_logs.extend(got)
                continue
            torsion.append((p, taus))

    if torsion:
        return ("needs torsion realisation (Parts I--II, milestone iii)",
                torsion)

    # residue at the hypertangent place at infinity (Lemma 8.1)
    if q is not None and len(gens) >= 2:
        tinf = _vinfty_residue(T, f, Y)
        if tinf is not None:
            if verbose:
                print(f"  v_oo (hypertangent top): delta = 1, v_oo(f) = -1, "
                      f"residue {tinf[0]} + ({tinf[1]})*y")
            lower = [g for g in gens[:-1]]
            nonconst = (_c(tinf[1]) != 0) or (_certify_nonconstant(tinf[0], lower) is True)
            if nonconst:
                return ("not elementary", "v_oo", tinf)

    # tower specials (Theorem 6.1): offered regardless of the integrand
    seen = {pp for pp, _ in unk_logs}
    cand = set()
    for dpair in list(T.derivs) + ([T.Dy] if q is not None else []):
        for comp in dpair:
            if comp == 0:
                continue
            for part in sp.fraction(sp.cancel(comp)):
                if not any(part.has(g) for g in gens):
                    continue
                for P_, _m in sp.factor_list(sp.Poly(part, *gens))[1]:
                    pp = P_.as_expr()
                    if any(pp.has(g) for g in gens):
                        cand.add(pp)
    for pp in sorted(cand, key=sp.default_sort_key):
        if pp in seen:
            continue
        if _classify(T, pp)[3]:
            unk_logs.append((pp, sp.S(0)))
            seen.add(pp)
            if verbose:
                print(f"  tower special: candidate log({pp})")

    # specials over Fbar (Theorem 6.1): on request, replace each special
    # p(g) with constant coefficients by its linear factors g - r
    if split_specials:
        new_logs = []
        for pp, _ in unk_logs:
            done_split = False
            for g in gens:
                P = sp.Poly(pp, g)
                if P.degree() >= 2 and all(c.free_symbols.isdisjoint(set(gens))
                                           for c in P.all_coeffs()):
                    rd = sp.roots(P)
                    if sum(rd.values()) == P.degree():
                        for r, m_ in rd.items():
                            new_logs.append((g - r, sp.S(0)))
                        done_split = True
                    break
            if not done_split:
                new_logs.append((pp, sp.S(0)))
        unk_logs = new_logs
        if verbose:
            print(f"  specials split over Fbar: {[pp for pp, _ in unk_logs]}")

    # residue-invisible unit candidates (Remark 7.7)
    units, units_complete = [], True
    if q is not None:
        for g in gens:
            if q.free_symbols <= {g} and sp.degree(q, g) % 2 == 0:
                uu = fundamental_unit(q, g)
                if uu is not None:
                    units.append((uu[0], uu[1], uu[2]))
                    if verbose:
                        print(f"  unit candidate: A + B*y with "
                              f"deg_{g} B = {sp.degree(uu[1], g)}")
                else:
                    cert, data = nontorsion_certificate(q, g)
                    if cert:
                        if verbose:
                            print(f"  unit search inconclusive; [oo+ - oo-] certified "
                                  f"non-torsion by reduction mod p: {data}")
                        units_complete = True   # no non-constant units exist
                    else:
                        units_complete = False  # inconclusive height bound
                break

    # residual integrand
    rem = f
    for tau, u in det_logs:
        ld = (_pdiv(T.D(u), u, q) if q is not None
              else (sp.cancel(T.D(u)[0] / u[0]), sp.S(0)))
        rem = _padd(rem, _pscale(-tau, ld))

    # ansatz
    if bounds is None:
        nb = [sp.Poly(sp.fraction(rem[i])[0], *gens) for i in (0, 1)]
        db = [sp.Poly(sp.fraction(rem[i])[1] * denv, *gens) for i in (0, 1)]
        bounds = [max([P.degree(g) for P in nb + db]) + 2 for g in gens]
    cs0, cs1, t0, t1 = [], [], [], []
    for alpha in _iproduct(*[range(b + 1) for b in bounds]):
        mono = sp.Mul(*[g ** a for g, a in zip(gens, alpha)])
        c0 = sp.Symbol('a_' + '_'.join(map(str, alpha)))
        cs0.append(c0); t0.append(c0 * mono)
        if q is not None:
            c1 = sp.Symbol('b_' + '_'.join(map(str, alpha)))
            cs1.append(c1); t1.append(c1 * mono)
    V = (sp.Add(*t0) / denv, sp.Add(*t1) / denv if q is not None else sp.S(0))
    # the system is assembled WITHOUT cancellation: with the unknown
    # coefficients present, cancel would run multivariate gcds in which the
    # unknowns count as variables (catastrophic over an algebraic extension),
    # and a spurious common factor only rescales an equation
    nc_add = lambda u_, v_: (sp.together(u_[0] + v_[0]), sp.together(u_[1] + v_[1]))
    nc_scale = lambda a_, u_: (a_ * u_[0], a_ * u_[1])
    E = nc_add(T.D(V), nc_scale(-1, rem))
    gammas = [sp.Symbol('gamma_%d' % i) for i in range(len(units))]
    for gm, (A, B, c) in zip(gammas, units):
        E = nc_add(E, nc_scale(gm, _pdiv(T.D((A, B)), (A, B), q)))
    betas = [sp.Symbol('beta_%d' % i) for i in range(len(unk_logs))]
    for bt, (s, _) in zip(betas, unk_logs):
        E = nc_add(E, nc_scale(bt, _pdiv(T.D((s, sp.S(0))), (s, sp.S(0)), q)
                               if q is not None else
                               (sp.cancel(T.D((s, sp.S(0)))[0] / s), sp.S(0))))
    eqs = []
    for comp in E:
        if comp != 0:
            eqs += sp.Poly(sp.fraction(sp.together(comp))[0], *gens).coeffs()
    unks = cs0 + cs1 + gammas + betas
    sol = sp.linsolve(eqs, unks)
    if not sol:
        g0 = gens[0]
        if (bounds_given is None and _HAVE_RN and q is not None and len(gens) == 1
                and q.free_symbols <= {g0} and not unk_logs and units_complete
                and T.derivs[0] == (sp.S(1), sp.S(0))
                and _residue_free(T, rem, Y)):                  # realisation verified
            # Part I, Cor. 7.4: exact bounds; if the system is still
            # inconsistent, the residual is a non-exact second-kind
            # differential (Part III: the holomorphic remainder)
            Lf = RadicalField(q.subs(g0, _rn.x), 2)
            frn = [sp.cancel(f[0].subs(g0, _rn.x)), sp.cancel(f[1].subs(g0, _rn.x))]
            B, info = exact_degree_bounds(Lf, frn)
            if verbose:
                print(f"  retrying with the exact degree bounds of Part I: {B}")
            r2 = parallel_integrate_mixed(f, T, bounds=[max(B)], verbose=False)
            if isinstance(r2, tuple) and r2[0] == "failed":
                return ("not elementary", "holomorphic remainder: residual "
                        "second-kind differential is not exact "
                        "(exact bounds of Part I)", B)
            return r2
        if not split_specials and any(
                sp.Poly(pp, g).degree() >= 2 for pp, _ in unk_logs for g in gens
                if sp.Poly(pp, g).degree() >= 0):
            return parallel_integrate_mixed(f, T, bounds=bounds_given, extension=extension,
                                            verbose=verbose, split_specials=True)
        return ("failed", "no solution within bounds", bounds)
    sub = dict(zip(unks, list(sol)[0]))
    frees = set().union(*[sp.sympify(v).free_symbols
                          for v in sub.values()]) & set(unks)
    sub = {k: sp.sympify(v).subs({fp: 0 for fp in frees})
           for k, v in sub.items()}
    assert all(_c(comp.subs(sub)) == 0 for comp in E if comp != 0)

    y = sp.sqrt(q) if q is not None else None
    def _surf(u):
        return u[0] + (u[1] * y if q is not None else 0)
    I = (sp.cancel(V[0].subs(sub))
         + (sp.cancel(V[1].subs(sub)) * y if q is not None else 0)
         + sum(tau * sp.log(_surf(u)) for tau, u in det_logs)
         + sum(sub[g] * sp.log(A + B * y)
               for g, (A, B, c) in zip(gammas, units))
         + sum(sub[b] * sp.log(s) for b, (s, _) in zip(betas, unk_logs)))
    return I
