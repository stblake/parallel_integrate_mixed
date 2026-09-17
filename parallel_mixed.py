"""parallel_mixed.py -- the merged pipeline (milestone (i)).

One generic ParallelIntegrateMixed covering m = 1 (no radical), m = 2 with
q squarefree over R = Q[g_1,...,g_k] (radical anywhere in the tower: the
derivatives D g_i are elements and may involve y), and m >= 3 with q
m-th-power-free.  Elements are coordinate tuples on the Trager basis
w_i = y^i/E_i of Part I: pairs (c0, c1) <-> c0 + c1*y for m <= 2, m-tuples
for m >= 3 (class _RadBasis: E_i, the multiplication table, D w_i = Lambda_i w_i).

Pipeline (paper section numbers):
  classification of every denominator prime by Definition 4.4 computed
  generically -- eta_P on the generators and Dy (Lemma 4.3), uniformiser
  p (unramified) or y (branch), delta_P = 1 + eta_P (Theorem 4.6);
  Hermite exponents and the special guess (Corollary 5.9); residues
  tau_P = e*(f h/Dh)|_P (Theorem 7.5) with curve splitting: linear
  primes split by sqrt(q mod p), quadratic primes split by y when
  disc = s^2 q (the norm identity N(2a g + b -+ s y) = 4a p realises
  the logands, Lemma 7.2); the constancy test; residues at primes
  of any degree in the residue field K[g]/(p) -- the residue polynomial, the
  residue classes as (prime, sheet polynomial), realisation by Hensel lifting
  and linear algebra over K(c); the canonical residue of Algorithm 2 at any
  pole order, run in kappa(P) with no root substitution
  (_canonical_residue_field) so a transcendental tower reproduces Bronstein's
  parallel Risch (pmint): a deep pole at a place with non-constant coordinates
  (delta = 1) or at a normal prime of delta >= 2 is a local Hermite reduction
  followed by the residue; unit candidates from
  pell (Remark 7.7); the pair-valued ansatz, linsolve, exact
  componentwise verification.

For m >= 3 (Fermat-type curves y^m = q): residues at every constant-
coefficient prime in the residue field with the m x m norm N(z - tau) and
the sheet from gcd(Y^m - q, c - tau(Y)); realisation by Hensel lifting of
the sheet to Y^m = q mod p^N and linear algebra, the N deg D_c poles
distributed over the s = gcd(m, deg q) places at infinity (Puiseux
expansions there); unit candidates from a bounded divisor search at
infinity (_units_general), which replaces the continued fraction of m = 2.

Reported, not computed: realisation of unequal split residues at
linear primes (torsion / norm search: Parts I--II, milestone iii);
critical branch residues; for m >= 3: S'-units over special primes, residue
classes carried by several but not all sheets over one root, partially
ramified branch primes (gcd(m, l_0) > 1), the non-torsion and
holomorphic-remainder certificates (both m = 2 in the paper).
"""

import sympy as sp

from itertools import product as _iproduct
from pell import fundamental_unit, nontorsion_certificate
try:                      # shared codebase with Parts I and III
    from weier import division_poly_order
    from rnrad2 import RadicalField, exact_degree_bounds
    import rnrad2 as _rn
    _HAVE_RN = True
except Exception:         # pragma: no cover
    _HAVE_RN = False
from sympy.polys.rings import ring as _ring


def _c_generic(e):
    """sympy's cancel over the extension of the constants of e: the route for
    a symbol-free constant or an input that is not a polynomial fraction."""
    try:
        return sp.cancel(e, extension=True)
    except Exception:
        return sp.cancel(e)


def _c(e):
    """Canonical form of a rational function of the generators: with rational
    constants sympy's cancel; with algebraic constants the cancellation in
    K[symbols] over the number field K of the constants, cached across calls
    (_field_for), with the denominator monic -- one primitive element per
    field instead of one per call, and no assumption queries on radicals."""
    e = sp.sympify(e)
    syms = sorted(e.free_symbols, key=sp.default_sort_key)
    if not syms:
        return _c_generic(e)
    try:
        n, d = e.as_numer_denom()
        Pn = sp.Poly(n, *syms, domain=sp.EX)
        Pd = sp.Poly(d, *syms, domain=sp.EX)
        atoms = _alg_atoms(Pn.coeffs() + Pd.coeffs())
        if not atoms:
            return sp.cancel(e)
        conv = _field_for(atoms)
        K = conv.K
        R = _ring(syms, K)[0]
        nR = R({mo: conv(c_) for mo, c_ in Pn.as_dict().items()})
        dR = R({mo: conv(c_) for mo, c_ in Pd.as_dict().items()})
        nR, dR = nR.cancel(dR)
        lc = dR.LC
        if lc != K.one:
            nR, dR = nR.quo_ground(lc), dR.quo_ground(lc)
        back = lambda P: sp.Add(*[conv.back(c_) * sp.Mul(*[s ** k for s, k in zip(syms, mo)])
                                  for mo, c_ in P.terms()])
        return back(nR) / back(dR)
    except (_NonAlgebraic, sp.PolynomialError, sp.polys.polyerrors.GeneratorsError,
            sp.polys.polyerrors.CoercionFailed):
        return _c_generic(e)


_FIELDS = {}                       # frozenset of algebraic atoms -> _KConv


def _field_for(atoms):
    """A cached _KConv whose field contains the given algebraic atoms: the
    one built for exactly these atoms, or a cached one built for a superset;
    otherwise a new field for these atoms (never a union: the field of two
    unrelated sets of constants can have a degree that makes its primitive
    element, and every conversion back to radicals, far more expensive than
    the two fields kept apart)."""
    key = frozenset(atoms)
    conv = _FIELDS.get(key)
    if conv is not None:
        return conv
    for k, c in _FIELDS.items():
        if key <= k:
            _FIELDS[key] = c
            return c
    conv = _FIELDS[key] = _KConv(list(sp.ordered(key)))
    _CONVS.setdefault(conv.K, conv)
    return conv



# ---------------------------------------------------------------- pairs

def _padd(u, v):  return tuple(_c(a + b) for a, b in zip(u, v))
def _pscale(a, u): return tuple(_c(a * b) for b in u)
def _pmul(u, v, q):
    return (_c(u[0] * v[0] + u[1] * v[1] * q),
            _c(u[0] * v[1] + u[1] * v[0]))
def _pdiv(u, v, q):
    N = _c(v[0] ** 2 - q * v[1] ** 2)
    w = _pmul(u, (v[0], -v[1]), q)
    return (_c(w[0] / N), _c(w[1] / N))

def _zeta(m):
    """A primitive m-th root of unity in radicals (-1 for m = 2)."""
    if m == 2:
        return sp.S(-1)
    z = sp.expand_complex(sp.exp(2 * sp.pi * sp.I / m))
    return z


def _mroot(a, m):
    """The principal m-th root of a (factored) constant or expression --
    sqrt for m = 2 -- with the real root for a negative rational and odd m."""
    a = sp.factor(a)
    if m == 2:
        return sp.sqrt(a)
    if a.is_Rational and a < 0 and m % 2 == 1:
        return -sp.Pow(-a, sp.Rational(1, m))
    return sp.Pow(a, sp.Rational(1, m))


def _compositions(n, s):
    """All tuples of s non-negative integers with sum n."""
    if s == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for rest in _compositions(n - first, s - 1):
            yield (first,) + rest


def _domain(consts):
    """The algebraic number field generated by the constants (a sympy Domain,
    cached by _field_for; its converter is reachable through _convK)."""
    return _field_for(_alg_atoms([sp.sympify(z) for z in consts])).K


_CONVS = {}                        # field -> its _KConv (filled by _field_for)


def _convK(K, e):
    """A constant expression as an element of K, by the field's converter
    (tree evaluation over the atoms) when K came from _field_for."""
    conv = _CONVS.get(K)
    return conv(e) if conv is not None else K.from_sympy(sp.sympify(e))


def _polyK(K, e, g):
    """Poly(expand(e), g, domain=K) with the coefficients converted by the
    field's converter instead of K.from_sympy (a field isomorphism per call)."""
    e = sp.expand(e)
    conv = _CONVS.get(K)
    if conv is None or e == 0:
        return sp.Poly(e, g, domain=K)
    P = sp.Poly(e, g, domain=sp.EX)
    return sp.Poly({mo: conv(c_) for mo, c_ in P.as_dict().items()}, g, domain=K)


# ---------------------------------------------------------------- one number field
# The linear system of the ansatz (the end of _pim) is assembled and solved
# over ONE algebraic number field K = Q(alpha) (Q when every constant is
# rational): the algebraic atoms of all the constants of the system (sqrt(2),
# I, sqrt(1 + sqrt(5)), ...) give a primitive element by a single
# construct_domain call, every constant is converted into K by tree evaluation
# over the atoms, and the polynomial arithmetic of the assembly runs in the
# sparse ring K[gens].  This is what sympy's linsolve does internally for the
# coefficients of a system; doing it for the assembly as well avoids
# expand/cancel/Poly on Expr with algebraic constants, each of which re-derives
# the field (or queries the assumptions of nested radicals).

class _NonAlgebraic(Exception):
    """a constant of the linear system is not an algebraic number"""


def _alg_atoms(exprs):
    """The algebraic atoms of constant expressions: Rational leaves are
    dropped, Add and Mul are recursed, everything else (I, sqrt(2), a nested
    radical, a Pow of a sum) is an atom -- the classification of
    sympy.polys.constructor._construct_algebraic."""
    atoms = set()

    def walk(a):
        if a.is_Rational:
            return
        if a.is_Add or a.is_Mul:
            for b in a.args:
                walk(b)
        elif a.is_Pow and a.exp.is_Rational and a.exp.q > 1:
            atoms.add(sp.Pow(a.base, sp.Rational(1, a.exp.q)))   # b**(p/q) is (b**(1/q))**p
        else:
            atoms.add(a)
    for e in exprs:
        walk(sp.sympify(e))
    return list(sp.ordered(atoms))


class _KConv:
    """The field K generated by a list of algebraic atoms (Q for the empty
    list), built by one construct_domain call, and the conversion of constant
    expressions into K by tree evaluation over the atoms (never K.from_sympy
    on a composite expression, which runs a field isomorphism per call)."""
    def __init__(self, atoms):
        from sympy.polys.constructor import construct_domain
        if atoms:
            try:
                K, elems = construct_domain(atoms, field=True, extension=True)
            except Exception as exc:
                raise _NonAlgebraic(str(exc))
            # QQ<alpha>, or QQ_I (the Gaussian rationals) for the atom I alone
            if not (K.is_Field and K.is_Numerical and not (K.is_RR or K.is_CC)):
                raise _NonAlgebraic(f"domain {K}")
            self.map = dict(zip(atoms, elems))
        else:
            K, self.map = sp.QQ, {}
        self.K = K
        self.memo = {}
        self.back_memo = {}

    def back(self, a):
        """K.to_sympy, memoised: the same constants recur in every column."""
        r = self.back_memo.get(a)
        if r is None:
            r = self.back_memo[a] = self.K.to_sympy(a)
        return r

    def __call__(self, e):
        e = sp.sympify(e)
        r = self.memo.get(e)
        if r is not None:
            return r
        K = self.K
        if e.is_Rational:
            r = K.from_sympy(e)
        elif e.is_Add:
            r = K.zero
            for a in e.args:
                r = r + self(a)
        elif e.is_Mul:
            r = K.one
            for a in e.args:
                r = r * self(a)
        elif e in self.map:
            r = self.map[e]
        elif e.is_Pow and e.exp.is_Rational and e.exp.q > 1 and \
                sp.Pow(e.base, sp.Rational(1, e.exp.q)) in self.map:
            root = self.map[sp.Pow(e.base, sp.Rational(1, e.exp.q))]
            p_ = e.exp.p
            r = root ** abs(p_)
            if p_ < 0:
                r = K.one / r
        else:
            try:                              # an atom not seen when K was built
                r = K.from_sympy(e)
            except Exception as exc:
                raise _NonAlgebraic(f"{e}: {exc}")
        self.memo[e] = r
        return r


def _parts(exprs):
    """Numerators and denominators of rational functions (for _coeffs_in)."""
    out = []
    for e in exprs:
        out.extend(sp.fraction(sp.sympify(e)))
    return out


def _coeffs_in(gens, exprs):
    """The constant coefficients of polynomial expressions in gens."""
    cs = []
    for e in exprs:
        e = sp.sympify(e)
        if e == 0:
            continue
        cs.extend(sp.Poly(e, *gens, domain=sp.EX).coeffs())
    return cs


def _to_ring(R, conv, expr):
    """A polynomial expression in the generators of R as an element of R."""
    expr = sp.sympify(expr)
    if expr == 0:
        return R.zero
    P = sp.Poly(expr, *R.symbols, domain=sp.EX)
    return R({monom: conv(c) for monom, c in P.as_dict().items()})


class _FieldSystem:
    """The linear system A x = b of the ansatz over the field K: A a sparse
    DomainMatrix whose columns are the unknowns in the order of unks, b the
    residual; css/alphas/denvR reconstruct the rational part of the answer."""
    def __init__(self, K, R, A, b, unks, css, alphas, denvR):
        self.K, self.R, self.A, self.b = K, R, A, b
        self.unks, self.css, self.alphas, self.denvR = unks, css, alphas, denvR
        self.col = {u: j for j, u in enumerate(unks)}
        self.xs = None

    def solve(self):
        """The particular solution with the non-pivot unknowns 0 -- the
        solution linsolve returns once its free parameters are set to 0 (the
        reduced row echelon form is unique for a fixed column order) -- as a
        substitution dict, or None when the system is inconsistent.  The
        solution is verified on the matrix, exactly over K."""
        from sympy.polys.matrices import DomainMatrix
        K = self.K
        nrows, ncols = self.A.shape
        xs = [K.zero] * ncols
        if nrows:
            rref, pivots = self.A.hstack(self.b).rref()
            if ncols in pivots:
                return None
            sdm = rref.rep.to_sdm()
            for k, p in enumerate(pivots):
                xs[p] = sdm.get(k, {}).get(ncols, K.zero)
            x = DomainMatrix({i: {0: v} for i, v in enumerate(xs) if v != K.zero},
                             (ncols, 1), K)
            assert (self.A.matmul(x) - self.b).is_zero_matrix    # the linear equations, exactly
        self.xs = xs
        return {u: K.to_sympy(v) for u, v in zip(self.unks, xs)}

    def rational_part(self):
        """(sum_alpha c_alpha mono_alpha) / D_v per coordinate, cancelled in K[gens]."""
        out = []
        for cs in self.css:
            d = {}
            for alpha, c in zip(self.alphas, cs):
                v = self.xs[self.col[c]]
                if v != self.K.zero:
                    d[alpha] = v
            if not d:
                out.append(sp.S(0))
                continue
            num, den = self.R(d).cancel(self.denvR)
            out.append(num.as_expr() / den.as_expr())
        return tuple(out)


def _assemble_field(T, rem, denv, cols, css, alphas, unks):
    """The linear system of the ansatz over one number field (a _FieldSystem):
    the columns of the monomials m/D_v and m y/D_v by polynomial arithmetic in
    K[gens] over the one denominator Lfix = D_v^2 Dden 2q (m <= 2; the tower
    derivation on the Trager basis for m >= 3), the unit and special columns
    D u / u once each, all brought over a common denominator per coordinate,
    the equations read off monomial by monomial.  Raises _NonAlgebraic when a
    constant is not an algebraic number (the caller then takes the Expr route,
    which is also the route documented in _assemble_expr)."""
    from sympy.polys.matrices import DomainMatrix
    gens, q, m = T.gens, T.q, T.m
    nc = len(css)
    # the unknown-free pieces of the system, as expressions
    gd = [(sp.fraction(_c(d[0])), sp.fraction(_c(d[1]))) for d in T.derivs]
    pieces = [x for pair in gd for fr in pair for x in fr]
    Qh_fr = None
    if q is not None:
        Qh = T._Dhat(q)                               # D q = Qh0 + Qh1 y
        Qh_fr = (sp.fraction(_c(Qh[0])), sp.fraction(_c(Qh[1])))
        pieces += [q] + [x for fr in Qh_fr for x in fr]
    denv_factors = []
    for fac in sp.Mul.make_args(sp.sympify(denv)):
        base, ex = fac.as_base_exp()
        if not (ex.is_Integer and ex > 0):
            raise _NonAlgebraic(f"D_v factor {fac}")
        denv_factors.append((base, int(ex)))
    pieces += [b for b, _ in denv_factors]
    rem_fr = [sp.fraction(_c(rem[i])) for i in range(nc)]
    pieces += [x for fr in rem_fr for x in fr]
    col_fr = [(sym, frs) for sym, (col, frs) in cols]     # from _Analysis.column
    pieces += [x for _, frs in col_fr for fr in frs for x in fr]
    mono_cols = []
    if m >= 3:
        # D(mono w_i / D_v) by the tower derivation, unknown-free, one
        # cancelled tuple per basis element of the ansatz
        for i in range(nc):
            for ci, alpha in zip(css[i], alphas):
                mono = sp.Mul(*[g ** a for g, a in zip(gens, alpha)])
                col = T.D(_pscale(mono / denv, T.unit(i)))
                for j in range(nc):
                    fr = sp.fraction(_c(col[j]))
                    mono_cols.append((ci, j, fr))
                    pieces += list(fr)
    # the field and the ring
    conv = _field_for(_alg_atoms(_coeffs_in(gens, pieces)))
    K = conv.K
    R = _ring(gens, K)[0]
    toR = lambda e: _to_ring(R, conv, e)
    # Dden: the lcm of the denominators of the D g (a gcd in K[gens] is cheap,
    # unlike the Expr gcd over an algebraic extension the Expr route avoids)
    dens_g = []
    for (n0_, d0_), (n1_, d1_) in gd:
        for dd in (d0_, d1_):
            if dd not in dens_g:
                dens_g.append(dd)
    DdenR = R.one
    for dd in dens_g:
        DdenR = DdenR.lcm(toR(dd))
    Dg0s = [toR(n0_) * DdenR.exquo(toR(d0_)) for (n0_, d0_), _ in gd]
    Dg1s = [toR(n1_) * DdenR.exquo(toR(d1_)) for _, (n1_, d1_) in gd]
    denvR = R.one
    for base, ex in denv_factors:
        denvR = denvR * toR(base) ** ex
    if q is not None:
        qR = toR(q)
        Qs0 = toR(Qh_fr[0][0]) * DdenR.exquo(toR(Qh_fr[0][1]))
        Qs1 = toR(Qh_fr[1][0]) * DdenR.exquo(toR(Qh_fr[1][1]))
        Lfix = denvR ** 2 * DdenR * qR * 2
    else:
        Lfix = denvR ** 2 * DdenR
    ddenv = [denvR.diff(gR) for gR in R.gens]
    parts_by = [[] for _ in range(nc)]             # per coordinate: (unknown, (num, den))
    if m <= 2:
        # D(m/D_v) = sum_g (dm/dg D_v - m dD_v/dg) D g / D_v^2 over the one
        # denominator Lfix, so no cancellation is run per monomial
        monoRs = [R({alpha: K.one}) for alpha in alphas]
        for c0, monoR in zip(css[0], monoRs):
            cg = [monoR.diff(gR) * denvR - monoR * dg for gR, dg in zip(R.gens, ddenv)]
            n0, n1 = R.zero, R.zero
            for c_, D0, D1 in zip(cg, Dg0s, Dg1s):
                n0 = n0 + c_ * D0
                n1 = n1 + c_ * D1
            if q is not None:
                n0, n1 = n0 * qR * 2, n1 * qR * 2
            parts_by[0].append((c0, (n0, Lfix)))
            if nc > 1:
                parts_by[1].append((c0, (n1, Lfix)))
        if q is not None:
            for c1, monoR in zip(css[1], monoRs):
                cg = [monoR.diff(gR) * denvR - monoR * dg for gR, dg in zip(R.gens, ddenv)]
                s0, s1 = R.zero, R.zero
                for c_, D0, D1 in zip(cg, Dg0s, Dg1s):
                    s0 = s0 + c_ * D0
                    s1 = s1 + c_ * D1
                # D(m y/D_v) = c.(Dg0 + Dg1 y) y + (m/D_v)(Dy0 + Dy1 y),  y^2 = q
                n0 = s1 * qR * qR * 2 + monoR * denvR * Qs1 * qR
                n1 = s0 * qR * 2 + monoR * denvR * Qs0
                parts_by[0].append((c1, (n0, Lfix)))
                parts_by[1].append((c1, (n1, Lfix)))
    else:
        for ci, j, (n_, d_) in mono_cols:
            parts_by[j].append((ci, (toR(n_), toR(d_))))
    for sym, frs in col_fr:
        for i in range(nc):
            n_, d_ = frs[i]
            parts_by[i].append((sym, (toR(n_), toR(d_))))
    remR = [(toR(n_), toR(d_)) for n_, d_ in rem_fr]
    # the equations: per coordinate, every column times the quotient of the
    # common denominator by its own, read off monomial by monomial
    col_index = {u: j for j, u in enumerate(unks)}
    ncols = len(unks)
    rows, rhs, nrows = {}, {}, 0
    for i in range(nc):
        parts = parts_by[i]
        rn, rd = remR[i]
        distinct = []
        for _, (_, dd) in parts + [(None, (rn, rd))]:
            if not any(dd == d2 for d2 in distinct):
                distinct.append(dd)
        L = R.one                                  # the common denominator (unknown-free)
        for dd in distinct:
            L = L.lcm(dd)
        quo = [L.exquo(dd) for dd in distinct]

        def dindex(dd):
            return next(k for k, d2 in enumerate(distinct) if d2 == dd)
        row_of = {}
        for sym, (nn, dd) in parts:
            if not nn:
                continue
            poly = nn * quo[dindex(dd)]
            j = col_index[sym]
            for monom, coeff in poly.terms():
                r = row_of.get(monom)
                if r is None:
                    r = row_of[monom] = nrows
                    nrows += 1
                rows.setdefault(r, {})[j] = coeff
        for monom, coeff in (rn * quo[dindex(rd)]).terms():
            r = row_of.get(monom)
            if r is None:
                r = row_of[monom] = nrows
                nrows += 1
            rhs[r] = coeff
    A = DomainMatrix(rows, (nrows, ncols), K)
    b = DomainMatrix({r: {0: v} for r, v in rhs.items()}, (nrows, 1), K)
    return _FieldSystem(K, R, A, b, unks, css, alphas, denvR)


def _assemble_expr(T, rem, denv, cols, css, monos):
    """The equations of the ansatz by Expr arithmetic -- the route taken when
    a constant of the system is not an algebraic number (_NonAlgebraic).  The
    columns are the same unknown-free tuples as in _assemble_field; the
    coordinates are brought over a common denominator by polynomial
    arithmetic and the equations are the coefficients of the monomials."""
    gens, q, m = T.gens, T.q, T.m
    nc = len(css)
    columns = []                                   # (unknown, tuple) -- D(basis element)
    parts_by = [[] for _ in range(nc)]             # per coordinate: (unknown, (num, den))
    if m <= 2:
        # the monomial columns by polynomial arithmetic alone: with Dden a common
        # multiple of the denominators of the Dg (and of Dq), every D(m/D_v) and
        # D(m y/D_v) is a pair of polynomials over the ONE denominator
        #     Lfix = D_v^2 * Dden * (2q),
        # so no cancellation is run per monomial (which, over an algebraic
        # extension, is what the assembly used to spend its time on)
        gd = [(sp.fraction(_c(d[0])), sp.fraction(_c(d[1]))) for d in T.derivs]
        dens_g = []
        for (n0_, d0_), (n1_, d1_) in gd:
            for dd in (d0_, d1_):
                if dd not in dens_g:
                    dens_g.append(dd)
        if any(_has_alg(dd) for dd in dens_g):
            Dden = sp.Mul(*dens_g)
        else:
            Dden = sp.S(1)
            for dd in dens_g:
                Dden = _c(Dden * dd / sp.gcd(Dden, dd))
        Dg0s = [sp.expand(_c(d[0] * Dden)) for d in T.derivs]
        Dg1s = [sp.expand(_c(d[1] * Dden)) for d in T.derivs]
        if q is not None:
            Qh = T._Dhat(q)                             # D q = Qh0 + Qh1 y ; Dy = (Qh1/2, Qh0/(2q))
            Qs0 = sp.expand(_c(Qh[0] * Dden)); Qs1 = sp.expand(_c(Qh[1] * Dden))
            Lfix = sp.expand(denv ** 2 * Dden * 2 * q)
        else:
            Lfix = sp.expand(denv ** 2 * Dden)
        ddenv = [sp.expand(sp.diff(denv, g)) for g in gens]
        for c0, mono in zip(css[0], monos):
            cg = [sp.expand(sp.diff(mono, g) * denv - mono * dg) for g, dg in zip(gens, ddenv)]
            n0 = sp.expand(sp.Add(*[c_ * D0 for c_, D0 in zip(cg, Dg0s)]))
            n1 = sp.expand(sp.Add(*[c_ * D1 for c_, D1 in zip(cg, Dg1s)]))
            if q is not None:
                n0, n1 = sp.expand(n0 * 2 * q), sp.expand(n1 * 2 * q)
            parts_by[0].append((c0, (n0, Lfix)))
            if nc > 1:
                parts_by[1].append((c0, (n1, Lfix)))
        if q is not None:
            for c1, mono in zip(css[1], monos):
                cg = [sp.expand(sp.diff(mono, g) * denv - mono * dg) for g, dg in zip(gens, ddenv)]
                s0 = sp.Add(*[c_ * D0 for c_, D0 in zip(cg, Dg0s)])
                s1 = sp.Add(*[c_ * D1 for c_, D1 in zip(cg, Dg1s)])
                # D(m y/D_v) = c.(Dg0 + Dg1 y) y + (m/D_v)(Dy0 + Dy1 y),  y^2 = q
                n0 = sp.expand(s1 * 2 * q * q + mono * denv * Qs1 * q)
                n1 = sp.expand(s0 * 2 * q + mono * denv * Qs0)
                parts_by[0].append((c1, (n0, Lfix)))
                parts_by[1].append((c1, (n1, Lfix)))
    else:
        # m >= 3: D(mono w_i / D_v) by the tower derivation on the Trager
        # basis, one cancelled tuple per basis element of the ansatz
        for i in range(nc):
            for ci, mono in zip(css[i], monos):
                col = T.D(_pscale(mono / denv, T.unit(i)))
                for j in range(nc):
                    parts_by[j].append((ci, sp.fraction(_c(col[j]))))
    columns = [(sym, col) for sym, (col, frs) in cols]     # from _Analysis.column
    eqs = []
    for i in range(nc):
        parts = list(parts_by[i])
        parts += [(sym, sp.fraction(_c(pr[i]))) for sym, pr in columns]
        rn, rd = sp.fraction(_c(rem[i]))
        # the denominators are few and repeated (Lfix for every monomial):
        # the lcm and the quotients are computed once per distinct denominator
        distinct = []
        for _, (_, dd) in parts + [(None, (rn, rd))]:
            if dd not in distinct:
                distinct.append(dd)
        # with algebraic constants in the denominators SymPy's gcd is very slow
        # (nested radicals): the product of the distinct denominators is then
        # used as the common denominator -- a multiple of the lcm, which only
        # scales the equations by a polynomial and changes no solution
        if any(_has_alg(dd) for dd in distinct):
            L = sp.Mul(*distinct)
            quo = {dd: sp.Mul(*[d2 for d2 in distinct if d2 is not dd]) for dd in distinct}
        else:
            L = sp.S(1)                            # common denominator (unknown-free)
            for dd in distinct:
                L = _c(L * dd / sp.gcd(L, dd))
            quo = {dd: _c(L / dd) for dd in distinct}
        total = sp.S(0)
        for sym, (nn, dd) in parts:
            if nn != 0:
                total += sym * sp.expand(nn * quo[dd])
        total -= sp.expand(rn * quo[rd])
        if total != 0:
            try:
                eqs += sp.Poly(total, *gens).coeffs()
            except sp.PolynomialError:             # an exact quotient was missed: the general route
                eqs += sp.Poly(sp.fraction(sp.together(total))[0], *gens).coeffs()
    return eqs


class _RadBasis:
    """The Trager basis w_i = y^i / E_i (i < m) of the integral closure of
    R = F[gens] in K(y), y^m = q, for q m-th-power-free with squarefree
    decomposition q = lc prod_l Q_l^l (Part I, Prop. 3.2):
        E_i = prod_l Q_l^floor(i l / m),
        w_i w_k = c_{ik} w_{(i+k) mod m},  c_{ik} = E_{i+k}/(E_i E_k)  (i + k < m)
                                            c_{ik} = q E_{i+k-m}/(E_i E_k)  (i + k >= m),
    both c_{ik} polynomials.  Elements are m-tuples of coordinates in K."""
    def __init__(self, q, m, gens):
        self.q, self.m, self.gens = q, m, list(gens)
        _, sfl = sp.sqf_list(sp.expand(q), *gens)
        Q = {}
        for fac, l in sfl:
            if l >= m:
                raise ValueError(f"radicand {q} is not {m}-th-power-free")
            Q[l] = Q.get(l, sp.S(1)) * fac
        self.Q = Q
        self.E = [sp.expand(sp.Mul(*[Ql ** (i * l // m) for l, Ql in Q.items()])) for i in range(m)]
        self.mul = {}
        for i in range(m):
            for k in range(m):
                if i + k < m:
                    coef = self.E[i + k] / (self.E[i] * self.E[k])
                else:
                    coef = q * self.E[i + k - m] / (self.E[i] * self.E[k])
                self.mul[(i, k)] = ((i + k) % m, sp.expand(sp.cancel(coef)))

    def zero(self):
        return (sp.S(0),) * self.m

    def times_w(self, t, i):
        """the tuple t times the basis element w_i"""
        r = [sp.S(0)] * self.m
        for k in range(self.m):
            if t[k] == 0:
                continue
            idx, coef = self.mul[(k, i)]
            r[idx] += t[k] * coef
        return tuple(_c(z) for z in r)

    def mult(self, u, v):
        r = [sp.S(0)] * self.m
        for i in range(self.m):
            if u[i] == 0:
                continue
            for k in range(self.m):
                if v[k] == 0:
                    continue
                idx, coef = self.mul[(i, k)]
                r[idx] += u[i] * v[k] * coef
        return tuple(_c(z) for z in r)

    def matrix(self, v):
        """M with M[j, k] = coordinate j of v w_k (multiplication by v)"""
        M = sp.zeros(self.m, self.m)
        for k in range(self.m):
            col = self.times_w(v, k)
            for j in range(self.m):
                M[j, k] = col[j]
        return M

    def div(self, u, v):
        """u / v: the solution of M_v z = u by the adjugate of M_v (division-
        free, so no intermediate fractions with algebraic coefficients)"""
        if all(v[k] == 0 for k in range(1, self.m)):
            return tuple(_c(z / v[0]) for z in u)
        M = self.matrix(v)
        dens = [sp.fraction(sp.together(M[j, k]))[1] for j in range(self.m) for k in range(self.m)]
        L = sp.S(1)
        for dd in dens:
            L = sp.lcm(L, dd)
        if L != 1:
            M = M.applyfunc(lambda z: sp.cancel(z * L))
        adj = M.adjugate(method='berkowitz')
        det = M.det(method='berkowitz')
        uv = sp.Matrix(list(u))
        return tuple(_c(L * sum(adj[j, k] * uv[k] for k in range(self.m)) / det) for j in range(self.m))

    def norm(self, v):
        return _c(self.matrix(v).det(method='berkowitz'))

    def from_Y(self, expr, Y):
        """coordinates of an expression rational in the generators and Y,
        Y^m = q: numerator and denominator reduced modulo Y^m - q, then the
        quotient taken in the basis (y^i = E_i w_i)"""
        e = sp.together(sp.expand(expr))
        n, d = sp.fraction(e)
        PY = sp.Poly(Y ** self.m - self.q, Y)
        def tup(z):
            P = sp.rem(sp.Poly(sp.expand(z), Y), PY)
            return tuple(_c(P.coeff_monomial(Y ** i) * self.E[i]) for i in range(self.m))
        return self.div(tup(n), tup(d))

    def to_Y(self, u, Y):
        return sp.Add(*[u[i] * Y ** i / self.E[i] for i in range(self.m)])


class Tower:
    """gens with derivative tuples; q = None means m = 1 (elements are pairs
    (a, 0)); m = 2: pairs a + b y on the basis (1, y), q squarefree; m >= 3:
    m-tuples on the Trager basis w_i = y^i/E_i (q m-th-power-free)."""
    def __init__(self, gens, derivs, q=None, m=2):
        self.gens, self.q = list(gens), q
        self.m = 1 if q is None else m
        self.n = 2 if self.m <= 2 else self.m          # length of the coordinate tuples
        self.derivs = [tuple(sp.cancel(c) for c in self._pad(d)) for d in derivs]
        self.basis = None
        self.E = [sp.S(1)] * self.n
        if q is not None and self.m == 2:
            Q = self._Dhat(q)
            self.Dy = (sp.cancel(Q[1] / 2), sp.cancel(Q[0] / (2 * q)))
            self.Dw = [(sp.S(0), sp.S(0)), self.Dy]
        elif q is not None:
            self.basis = _RadBasis(q, self.m, self.gens)
            self.E = self.basis.E
            Qh = self._Dhat(q)
            # D w_i = Lambda_i w_i,  Lambda_i = (i/m) Dq/q - D E_i / E_i
            self.Lam = []
            for i in range(self.m):
                lam = _pscale(sp.Rational(i, self.m) / q, Qh)
                if self.E[i] != 1:
                    lam = _padd(lam, _pscale(-1 / self.E[i], self._Dhat(self.E[i])))
                self.Lam.append(lam)
            self.Dw = [self.D(self.unit(i)) for i in range(self.m)]
            self.Dy = self.Dw[1]
    def _pad(self, u):
        u = tuple(u)
        return u + (sp.S(0),) * (self.n - len(u)) if len(u) < self.n else u
    def zero(self):
        return (sp.S(0),) * self.n
    def unit(self, i):
        return tuple(sp.S(1) if j == i else sp.S(0) for j in range(self.n))
    def scalar(self, a):
        return (sp.sympify(a),) + (sp.S(0),) * (self.n - 1)
    def _Dhat(self, c):
        out = self.zero()
        for g, d in zip(self.gens, self.derivs):
            out = _padd(out, _pscale(sp.diff(c, g), d))
        return out
    def D(self, u):
        u = self._pad(u)
        out = self._Dhat(u[0])
        if self.q is None:
            return out
        if self.m == 2:
            h1 = self._Dhat(u[1])
            out = _padd(out, _pmul(h1, (sp.S(0), sp.S(1)), self.q))
            return _padd(out, _pscale(u[1], self.Dy))
        for i in range(1, self.m):
            if u[i] == 0:
                continue
            t = _padd(self._Dhat(u[i]), _pscale(u[i], self.Lam[i]))
            out = _padd(out, self.basis.times_w(t, i))
        return out
    def mul(self, u, v):
        if self.q is None:
            return (_c(u[0] * v[0]), sp.S(0))
        if self.m == 2:
            return _pmul(u, v, self.q)
        return self.basis.mult(self._pad(u), self._pad(v))
    def div(self, u, v):
        if self.q is None:
            return (_c(u[0] / v[0]), sp.S(0))
        if self.m == 2:
            return _pdiv(u, v, self.q)
        return self.basis.div(self._pad(u), self._pad(v))
    def norm(self, u):
        if self.q is None:
            return _c(u[0])
        if self.m == 2:
            return _c(u[0] ** 2 - self.q * u[1] ** 2)
        return self.basis.norm(self._pad(u))
    def from_Y(self, expr, Y):
        if self.q is None:
            return (_c(expr), sp.S(0))
        if self.m == 2:
            return _pair_reduce(expr, Y, self.q)
        return self.basis.from_Y(expr, Y)
    def to_Y(self, u, Y):
        if self.q is None:
            return u[0]
        if self.m == 2:
            return u[0] + u[1] * Y
        return self.basis.to_Y(self._pad(u), Y)
    def branch_mult(self, p):
        """l_0 with p | Q_{l_0} (the multiplicity of p in q); 0 if unramified"""
        return 0 if self.q is None else _vp(self.q, p, self.gens)

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
    """v_P of the tuple u at the prime(s) P over p (Lemma 4.3 / Part I, S4):
    unramified: min_i v_p(u_i); branch, p | Q_{l_0} with gcd(m, l_0) = 1
    (e_P = m, v_P(y) = l_0, v_P(w_i) = i l_0 mod m): min_i (m v_p(u_i) +
    (i l_0 mod m)), the summands having distinct valuations mod m."""
    g = T.gens
    if T.q is None:
        return _vp(u[0], p, g)
    if not branch:
        return min(_vp(u[i], p, g) for i in range(T.n))
    if T.m == 2:
        return min(2 * _vp(u[0], p, g), 2 * _vp(u[1], p, g) + 1)
    l0 = T.branch_mult(p)
    if sp.igcd(T.m, l0) != 1:
        raise NotImplementedError(f"partially ramified branch prime ({p}): gcd(m, l_0) = {sp.igcd(T.m, l0)} > 1")
    return min(T.m * _vp(u[i], p, g) + (i * l0) % T.m for i in range(T.m))

def _eta(T, p, branch):
    vals = [-_vP(d, p, T, branch) for d in T.derivs]
    if T.q is not None:
        vals += [-_vP(dw, p, T, branch) for dw in T.Dw[1:]]
    return max([0] + [v for v in vals if v is not sp.oo and v != -sp.oo])

def _classify(T, p):
    """(branch?, eta, delta, special?) at the prime(s) over p.  The uniformiser
    of the normality test is p (unramified) or w_{i*} with i* l_0 = 1 mod m
    (branch; y for m = 2)."""
    branch = T.q is not None and _vp(T.q, p, T.gens) > 0
    eta = _eta(T, p, branch)
    if branch:
        istar = 1 if T.m == 2 else pow(T.branch_mult(p), -1, T.m)
        pi = T.unit(istar)
    else:
        pi = T.scalar(p)
    special = eta + _vP(T.D(pi), p, T, branch) >= 1
    return branch, eta, 1 + eta, special

# -------------------------------------------------------------- residues

def _points_over(T, p):
    """Places over p as substitutions [(gen, root, yval)], via a generator
    in which p has degree <= 4; the m sheets over a root rho are
    y = zeta^k q(rho)^(1/m); yval is None for m = 1."""
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
            zeta = _zeta(T.m) if T.q is not None else None
            for rho in roots:
                if T.q is None:
                    pts.append((g, rho, None))
                    continue
                qbar = sp.cancel(T.q.subs(g, rho))
                r = _mroot(qbar, T.m)
                for k in range(T.m):
                    yv = r if k == 0 else (zeta ** k * r if T.m == 2 else sp.expand(zeta ** k * r))
                    pts.append((g, rho, yv))
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
    if T.q is None:
        # no curve: every place over p is the principal prime (g - rho)
        return [(tt, (g - rho, sp.S(0))) for (_, rho, _), tt in zip(pts, taus) if tt != 0]
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
    return None



def _realise_joint(T, pending, Y, verbose=False):
    """Corollary 7.6 for a residue divisor supported over several primes
    p_1, ..., p_r of R_0 at once: a logand u = a + b y with
    N(u) = c (p_1 ... p_r)^k need not have its norm supported on a single
    p_i (e.g. N(sqrt2 x + y) = -(x-1)^2 (x+1)^2 on y^2 = x^4 + 1), so the
    prime-by-prime search of _realise_points misses it.  pending is a list
    of (p, pts, taus); returns [(coeff, u_pair)] realising every nonzero
    residue, or None."""
    if T.q is None or len(pending) < 2:
        return None
    g = pending[0][1][0][0]
    if not T.q.free_symbols <= {g} or any(pts[0][0] != g for _, pts, _ in pending):
        return None
    P = sp.Mul(*[p for p, _, _ in pending])
    allpts = [(pt, tt) for _, pts, taus in pending for pt, tt in zip(pts, taus)]
    for a, b, c, k in _norm_search_all(T.q, P, g, kmax=2, dbmax=2):
        out, ok, covered = [], True, set()
        for sg in (1, -1):
            uu = (a, sg * b)
            hits = [(i, tt) for i, (pt, tt) in enumerate(allpts)
                    if _iszero(_reduce_at(uu[0] + uu[1] * Y, pt, Y))]
            gammas = [sp.nsimplify(tt / _vanish_order(T, uu, allpts[i][0], Y), [sp.sqrt(2), sp.sqrt(3)])
                      for i, tt in hits]
            if not (gammas and all(sp.simplify(gg - gammas[0]) == 0 for gg in gammas)):
                ok = False
                break
            covered.update(i for i, _ in hits)
            if gammas[0] != 0:
                out.append((gammas[0], uu))
        if ok and all(i in covered for i, (pt, tt) in enumerate(allpts) if tt != 0):
            if verbose:
                for gm, uu in out:
                    print(f"      joint norm factor {uu[0]} + ({uu[1]})*y over {P} "
                          f"(N = {c}*({P})**{k}): coefficient {gm}")
            return out
    return None


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
    tau = -(lim f/t)/eta in kappa(v_oo) = K_{n-1}(y), returned as a tuple.
    None if the top generator is not hypertangent or v_oo(f) != -1."""
    t = T.gens[-1]
    # Lemma 8.1 needs the hypertangent ABOVE the radical: q free of t, so
    # that t = oo is one place with residue field K_{n-1}(y) and y a unit
    # there.  With q depending on t the curve has its own places over
    # t = oo and the formula does not apply.
    if T.q is None or t in T.q.free_symbols:
        return None
    et = [sp.cancel(c / (1 + t ** 2)) for c in T.derivs[-1]]
    if any(c.has(t) for c in et) or all(c == 0 for c in et):
        return None
    def vinf(c):
        c = sp.cancel(c)
        if c == 0:
            return None
        n, d = sp.fraction(c)
        return sp.degree(d, t) - sp.degree(n, t)
    vs = [v for v in (vinf(c) for c in f) if v is not None]
    if not vs or min(vs) != -1:
        return None
    def lead(c):
        c = sp.cancel(c)
        if c == 0 or vinf(c) != -1:
            return sp.S(0)
        n, d = sp.fraction(c)
        return sp.cancel(sp.LC(n, t) / sp.LC(d, t))
    ct = tuple(lead(c) for c in f)
    tau = T.div(ct, tuple(et))
    return tuple(_c(-c) for c in tau)

def _deep_residues(T, f, p, pts, Y):
    """Laurent residues at a delta = 1 normal prime with a pole of order
    >= 2 (well-defined: exact parts contribute none).  Single-generator
    slice: requires gens = [g] with Dg = 1."""
    g = T.gens[0]
    e = sp.Dummy('e')
    m = T.m
    out = []
    for (gv, rho, yval) in pts:
        r = _mroot(T.q.subs(g, rho), m)
        eps = sp.simplify(sp.cancel(yval / r))
        yser = eps * sp.Pow(T.q.subs(g, rho + e), sp.Rational(1, m))
        floc = sp.Add(*[f[i].subs(g, rho + e) * yser ** i / T.E[i].subs(g, rho + e)
                        for i in range(T.n)])
        ser = sp.series(floc, e, 0, 1).removeO()
        out.append(_resfmt(ser.coeff(e, -1)))
    return out



def _has_alg(e):
    """does the expression carry algebraic constants (I, sqrt(5), 2**(1/4), ...)?"""
    e = sp.sympify(e)
    if e.has(sp.I):
        return True
    return any(isinstance(a, sp.Pow) and a.exp.is_Rational and not a.exp.is_Integer
               and not a.base.free_symbols for a in e.atoms(sp.Pow))


def _canonical_residues(T, f, p, pts, Y, verbose=False):
    """Algorithm 2 (Proposition 7.7, the canonical residue) at the places over
    an unramified normal prime p with delta = 1 and constant coordinates, in
    any tower: with pi = g - rho the local Hermite reduction
        f <- f - D(c pi^{-k}),   c = -mu/(k lambda_P),
    is run with the exact derivation of the tower -- the upper generators in
    the lift c are differentiated -- until the pole is simple, and the residue
    (f pi/D pi)|_P is read off.  The leading class mu of pi^{k+1} f in kappa(P)
    is read from the local expansion of f (y expanded about the place).
    Returns the list of residues (one per place), or None when the loop does
    not apply (non-constant coordinates, or q involving other generators)."""
    gens, q, m = T.gens, T.q, T.m
    g = pts[0][0]
    if q is not None and not q.free_symbols <= {g}:
        return None
    if any(sp.sympify(rho).free_symbols or (yv is not None and sp.sympify(yv).free_symbols)
           for _, rho, yv in pts):
        return None
    Dg = T.derivs[gens.index(g)]
    e = sp.Dummy('e')
    ncomp = T.n if q is not None else 1
    out = []
    for pt in pts:
        _, rho, yv = pt
        if q is not None:
            lam = _reduce_at(T.to_Y(Dg, Y), pt, Y)
            r = _mroot(q.subs(g, rho), m)
            eps = sp.simplify(sp.cancel(yv / r))
        else:
            lam = sp.cancel(Dg[0].subs(g, rho))
        fc = f
        tau = None
        for _ in range(16):
            k0 = max(-_vp(fc[i], p, gens) for i in range(ncomp))
            if k0 <= 0:
                tau = sp.S(0)
                break
            loc = fc[0].subs(g, rho + e)
            if q is not None:
                yser = eps * sp.series(sp.Pow(q.subs(g, rho + e), sp.Rational(1, m)), e, 0, k0 + 2).removeO()
                loc = loc + sp.Add(*[fc[i].subs(g, rho + e) * yser ** i / T.E[i].subs(g, rho + e)
                                     for i in range(1, ncomp)])
            ser = sp.series(loc, e, 0, 1).removeO()
            j, mu = 0, None
            for jj in range(k0, 0, -1):
                cj = sp.cancel(ser.coeff(e, -jj))
                if not _iszero(cj):
                    j, mu = jj, cj
                    break
            if mu is None:
                tau = sp.S(0)
                break
            if j == 1:
                tau = _resfmt(sp.cancel(mu / lam))
                break
            k = j - 1
            c = sp.cancel(-mu / (k * lam))
            w = T.scalar(sp.cancel(c / (g - rho) ** k))
            fc = _padd(fc, _pscale(-1, T.D(w)))
            if verbose:
                print(f"      Hermite step at ({rho}, y={yv}): order {j} -> subtract D({c} * ({g} - ({rho}))**(-{k}))")
        if tau is None:
            return None
        out.append(tau)
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


def _ell_ops(q, g, conv):
    """Chord-and-tangent group law on y^2 = q(g), deg q = 3, on the monic model
    X = c3 g, Ytil = c3 y, with the coordinates as elements of the number
    field K of conv (exact zero tests, no simplification).  Returns
    (to_m, add, c) with c the coefficients [c3, c2, c1, c0] of q in K."""
    K = conv.K
    c = [conv(z) for z in sp.Poly(q, g).all_coeffs()]     # [c3, c2, c1, c0]
    c3, a2, a4 = c[0], c[1], c[2] * c[0]                    # Ytil^2 = X^3 + a2 X^2 + a4 X + c0 c3^2
    two, three = K.convert(2), K.convert(3)

    def to_m(P):
        return (c3 * conv(P[0]), c3 * conv(P[1]))

    def add(P, Q):
        if P is None:
            return Q
        if Q is None:
            return P
        x1, y1 = P
        x2, y2 = Q
        if x1 == x2:
            if y1 + y2 == K.zero:
                return None
            lam = (three * x1 ** 2 + two * a2 * x1 + a4) / (two * y1)
        else:
            lam = (y2 - y1) / (x2 - x1)
        x3 = lam ** 2 - a2 - x1 - x2
        return (x3, lam * (x1 - x3) - y1)
    return to_m, add, c


def _torsion_order(q, g, P, conv, add, c, bound):
    """The order m <= bound of the point P (model coordinates of _ell_ops):
    by the division polynomials of Part III when the model is depressed,
    else by repeated addition; None if no order <= bound."""
    if _HAVE_RN and c[1] == conv.K.zero:
        cc = sp.Poly(q, g).all_coeffs()
        m = division_poly_order(cc[2] * cc[0], cc[3] * cc[0] ** 2,
                                conv.back(P[0]), conv.back(P[1]), Nmax=bound)
        if m is not None:
            return m
    kP = P
    for k in range(2, bound + 1):
        kP = add(kP, P)
        if kP is None:
            return k
    return None


def _ell_sum(q, g, Y, terms, conv, add, c):
    """The sum S of the points of terms = [(P, n)], n in Z, in the group law
    of _ell_ops, and the function h with div(h) = sum n (P - oo) - (S - oo):
    for S + P = R the line through S and P over the vertical through R has
    divisor S + P - R - oo, and -P = (x_P, -y_P) with div(x - x_P) =
    P + (-P) - 2 oo.  Accumulated in K[Y, g] modulo Y^2 - q; returns
    (S, (h0, h1)) with h = h0 + h1 y as rational functions of g cancelled in
    K[g].  With terms = [(P, m)], m the order of P, h is the Miller function
    with divisor m P - m oo."""
    K = conv.K
    R, YR, gR = _ring([Y, g], K)
    c3, a2, a4 = c[0], c[1], c[2] * c[0]
    two, three = K.convert(2), K.convert(3)
    qR = R({(0, k): conv(z) for (k,), z in sp.Poly(q, g).as_dict().items()})
    X0 = c3 * gR
    S, num, den = None, R.one, R.one
    for P, n in terms:
        if n < 0:
            P, n = (P[0], -P[1]), -n
            den *= (X0 - P[0]) ** n
        for _ in range(n):
            if S is None:
                S = P
                continue
            x1, y1 = S
            if x1 == P[0] and y1 + P[1] == K.zero:          # S = -P: the vertical line
                num, S = num * (X0 - x1), None
                continue
            lam = ((three * x1 ** 2 + two * a2 * x1 + a4) / (two * y1) if x1 == P[0]
                   else (P[1] - y1) / (P[0] - x1))
            num = (num * (c3 * YR - y1 - lam * (X0 - x1))).rem(YR ** 2 - qR)
            S = add(S, P)
            den *= X0 - S[0]
    parts = []
    for i in (0, 1):
        hi = R({(0, mo[1]): z for mo, z in num.terms() if mo[0] == i})
        n_, d_ = hi.cancel(den)
        expr = lambda Pl: sp.Add(*[conv.back(z) * g ** mo[1] for mo, z in Pl.terms()])
        parts.append(expr(n_) / expr(d_))
    return S, tuple(parts)


def _pair_reduce(e, Ysym, q):
    """Pair (a, b) = a + b*y of an expression rational in the generators and
    the symbol Ysym with Ysym**2 = q (denominator rationalised)."""
    e = sp.together(sp.expand(e))
    n, d = sp.fraction(e)
    red = lambda z: sp.rem(sp.Poly(sp.expand(z), Ysym), sp.Poly(Ysym ** 2 - q, Ysym)).as_expr()
    n, d = red(n), red(d)
    db = d.subs(Ysym, -Ysym)
    N, D0 = red(sp.expand(n * db)), red(sp.expand(d * db))
    return (_c(N.subs(Ysym, 0) / D0), _c(sp.expand(N).coeff(Ysym, 1) / D0))


def _torsion_order_and_miller(q, g, pt, Y, bound=24, verbose=False):
    """On y^2 = q(g), deg q = 3: the order m of [P - oo] for the place
    pt = (g, rho, y0) with constant coordinates and the Miller function h
    with div(h) = m P - m oo as a pair.  None if no order <= bound is found."""
    rho, yv = pt[1], pt[2]
    conv = _field_for(_alg_atoms([sp.sympify(rho), sp.sympify(yv)] + sp.Poly(q, g).all_coeffs()))
    to_m, add, c = _ell_ops(q, g, conv)
    P = to_m((rho, yv))
    m = _torsion_order(q, g, P, conv, add, c, bound)
    if m is None:
        return None
    return m, _ell_sum(q, g, Y, [(P, m)], conv, add, c)[1]


def _rational_point(q, g):
    """A rational point (g0, y0) on y^2 = q(g), deg q = 2, or None: small
    integers and half-integers first, then the points at infinity are used
    by the caller through the square leading coefficient."""
    for num in range(0, 13):
        for sgn in (1, -1):
            for den in (1, 2, 3):
                g0 = sp.Rational(sgn * num, den)
                v = q.subs(g, g0)
                y0 = sp.sqrt(v)
                if v >= 0 and y0.is_rational:
                    return g0, y0
    return None


def conic_to_line(T, f):
    """Rational parametrisation of a conic y^2 = q(g), deg q = 2, through a
    rational point (g0, y0): the pencil y = y0 + w (g - g0) meets the conic
    in the second point
        g = (2 y0 w - (q2 + w^2) g0 - q1) / (q2 - w^2),   y = y0 + w (g - g0),
    so the curve disappears and the whole tower is rewritten over Q(w)
    (w replaces g at its position, q becomes None).  Returns (T', f', back)
    with back the substitution w -> (y - y0)/(g - g0)."""
    gens, q = T.gens, T.q
    g = [gg for gg in gens if q.free_symbols <= {gg}][0]
    P = sp.Poly(q, g)
    q2, q1, q0 = [P.coeff_monomial(g ** k) for k in (2, 1, 0)]
    pt = _rational_point(q, g)
    if pt is None:
        return None
    g0, y0 = pt
    w = sp.Symbol('w_%s' % g.name, positive=True)
    Y = sp.Dummy('Y')
    g_new = sp.cancel((2 * y0 * w - (q2 + w ** 2) * g0 - q1) / (q2 - w ** 2))
    y_new = sp.cancel(y0 + w * (g_new - g0))
    def conv(pair):
        return (sp.cancel((pair[0] + pair[1] * Y).subs({g: g_new, Y: y_new})), sp.S(0))
    # D w = (Dy (g - g0) - (y - y0) Dg) / (g - g0)^2, as a pair, then rewritten
    Dg = T.derivs[gens.index(g)]
    num = _padd(_pscale(g - g0, T.Dy), _pscale(-1, _pmul((-y0, sp.S(1)), Dg, q)))
    Dw = _pscale(1 / (g - g0) ** 2, num)
    new_derivs = [conv(Dw if gg == g else d) for gg, d in zip(gens, T.derivs)]
    new_gens = [w if gg == g else gg for gg in gens]
    T2 = Tower(new_gens, new_derivs, q=None)
    f2 = conv(f)
    back = [(w, (sp.sqrt(q) - y0) / (g - g0))]
    return T2, f2, back

def quartic_to_cubic(T, f):
    """Change of model for a quartic radicand q(g) with a square leading
    coefficient (two rational places at infinity): with p the polynomial
    part of sqrt(q) and r = q - p^2 (deg r <= 2), the substitution
    s = y - p(g) gives 2 p(g) s = r(g) - s^2, a quadratic in g over Q(s)
    whose discriminant Delta(s) is a cubic; with T = 2 A'(s) g + B'(s),
    T^2 = Delta(s), and (g, y) -> (s, T) is birational.  The whole tower is
    rewritten in the new generators (s replaces g at its position); returns
    (T', f', back) with back the substitution rules s -> y - p(g),
    sqrt(Delta) -> 2 A' g + B' expressed in the old generators."""
    from pell import sqrt_polypart
    gens, q = T.gens, T.q
    g = [gg for gg in gens if q.free_symbols <= {gg}][0]
    p = sqrt_polypart(q, g)
    r = sp.expand(q - p ** 2)
    s, TT, Y = sp.Dummy('s'), sp.Dummy('T'), sp.Dummy('Y')
    P = sp.Poly(p, g); pc = P.all_coeffs()[::-1] + [0, 0, 0]          # ascending
    R = sp.Poly(r, g); rc = R.all_coeffs()[::-1] + [0, 0, 0]
    Ap = sp.expand(2 * pc[2] * s - rc[2]); Bp = sp.expand(2 * pc[1] * s - rc[1]); Cp = sp.expand(2 * pc[0] * s - rc[0] + s ** 2)
    Delta = sp.expand(Bp ** 2 - 4 * Ap * Cp)
    assert sp.degree(Delta, s) == 3
    g_new = _c((TT - Bp) / (2 * Ap))                                 # g in terms of (s, T)
    y_new = s + p.subs(g, g_new)                                        # y = s + p(g)
    def conv(pair):
        e = pair[0] + pair[1] * Y
        e = e.subs({g: g_new, Y: y_new})
        return _pair_reduce(e, TT, Delta)
    s_new = sp.Symbol('s_%s' % g.name, positive=True)
    # derivatives: Ds = Dy - p'(g) Dg ; DT = 2 A'(s) Ds g + 2 A' Dg + B'(s) Ds  (T = 2A'g + B')
    Dg = T.derivs[gens.index(g)]
    Dy = T.Dy
    Ds = _padd(Dy, _pscale(-sp.diff(p, g), Dg))
    new_derivs = []
    for gg, d in zip(gens, T.derivs):
        new_derivs.append(conv(Ds if gg == g else d))
    new_gens = [s_new if gg == g else gg for gg in gens]
    sub_s = lambda e: e.subs(s, s_new)
    new_derivs = [(sub_s(a), sub_s(b)) for a, b in new_derivs]
    T2 = Tower(new_gens, new_derivs, q=sub_s(Delta))
    f2 = conv(f); f2 = (sub_s(f2[0]), sub_s(f2[1]))
    # ordered: sqrt(Delta) -> 2 A'(s) g + B'(s) first (it introduces s), then s -> y - p(g)
    back = [(sp.sqrt(sub_s(Delta)), sub_s(2 * Ap * g + Bp)), (s_new, sp.sqrt(q) - p)]
    return T2, f2, back

def _qcoords(conv, e):
    """The coordinates over Q of a constant in the field of conv: on the
    power basis of the primitive element, (1, i) for QQ_I, (1) for QQ."""
    a = conv(e)
    if hasattr(a, 'to_list'):
        return [sp.QQ.to_sympy(z) for z in reversed(a.to_list())]
    if hasattr(a, 'x'):
        return [sp.QQ.to_sympy(a.x), sp.QQ.to_sympy(a.y)]
    return [sp.QQ.to_sympy(a)]


def _torsion_realise(T, pending, Y, bound=24, verbose=False):
    """Algorithm 3(d): the residue divisor of the pending primes
    [(p, pts, taus)] on an elliptic curve with one place at infinity (deg q
    = 3, constant coordinates).  A place whose class [P - oo] is torsion of
    order mu is realised on its own by its Miller function; the residues of
    the remaining places are decomposed over a Q-basis (beta_j) of their
    Q-span, tau_P = sum_j n_Pj beta_j with n_Pj in Z, so that the divisor
    is sum_j beta_j D_j with D_j = sum_P n_Pj (P - oo) of degree 0, and
    each D_j is realised by the group law: S_j = sum_P n_Pj P, mu_j the
    order of S_j (1 when S_j = oo), and _ell_sum on mu_j D_j gives u_j with
    div(u_j) = mu_j D_j, recorded with coefficient beta_j/mu_j.  Returns
    [(coefficient, pair)] or None (a class of order > bound, no cubic
    model, or a place with non-constant coordinates)."""
    g, q = pending[0][1][0][0], T.q
    if sp.degree(q, g) != 3 or not q.free_symbols <= {g} or any(pts[0][0] != g for _, pts, _ in pending):
        return None
    places = [(pt, tau) for _, pts, taus in pending for pt, tau in zip(pts, taus) if tau != 0]
    consts = [sp.sympify(z) for pt, tau in places for z in (pt[1], pt[2], tau)]
    if any(z.free_symbols for z in consts):
        return None
    conv = _field_for(_alg_atoms(consts + sp.Poly(q, g).all_coeffs()))
    to_m, add, c = _ell_ops(q, g, conv)

    def realise(terms):
        """(mu, u) with div(u) = mu * sum n (P - oo) for terms = [(P, n)], or None"""
        S = None
        for P, n in terms:
            for _ in range(abs(n)):
                S = add(S, P if n > 0 else (P[0], -P[1]))
        mu = 1 if S is None else _torsion_order(q, g, S, conv, add, c, bound)
        if mu is None:
            return None
        return mu, _ell_sum(q, g, Y, [(P, mu * n) for P, n in terms], conv, add, c)[1]

    out, rest = [], []
    for pt, tau in places:
        P = to_m((pt[1], pt[2]))
        got = realise([(P, 1)])
        if got is None:
            rest.append((pt, P, tau))
            continue
        out.append((tau / got[0], got[1]))
        if verbose:
            print(f"      torsion: [P - oo] of order {got[0]} at ({pt[1]}, {pt[2]}); "
                  f"Miller logand with coefficient {tau / got[0]}")
    if rest:
        rows = [_qcoords(conv, tau) for _, _, tau in rest]
        d = max(len(r) for r in rows)
        A = sp.Matrix([r + [0] * (d - len(r)) for r in rows]).T   # column i: the residue of rest[i]
        Rr, piv = A.rref()                                        # A[:, i] = sum_j Rr[j, i] A[:, piv[j]]
        for j, k in enumerate(piv):
            N = sp.ilcm(1, *[z.q for z in Rr.row(j)])
            ns = [int(N * Rr[j, i]) for i in range(len(rest))]
            terms = [(P, n) for (_, P, _), n in zip(rest, ns) if n]
            got = realise(terms)
            if got is None:
                return None
            beta = rest[k][2] / N
            out.append((beta / got[0], got[1]))
            if verbose:
                dv = ' + '.join(f"{n}*({pt[1]}, {pt[2]})" for (pt, _, _), n in zip(rest, ns) if n)
                print(f"      torsion: the divisor {dv} - ({sum(ns)}) oo has order {got[0]}; "
                      f"logand with coefficient {beta / got[0]}")
    return out


# ------------------------------------------ residues in the residue field

def _const_dir(T, p):
    """The generator g with p in K[g] (coefficients free of every generator)
    and, when there is a curve, q in K[g] as well; None otherwise."""
    G = set(T.gens)
    for g in T.gens:
        P = sp.Poly(p, g)
        if P.degree() >= 1 and all(sp.sympify(c).free_symbols.isdisjoint(G)
                                   for c in P.all_coeffs()):
            return g if (T.q is None or T.q.free_symbols <= {g}) else None
    return None


def _residue_dir(T, p):
    """A generator g in which p has positive degree, for the residue-field
    computation.  Prefers a constant-coefficient direction (_const_dir); for a
    transcendental tower (q = None) any direction with deg_g(p) >= 1 will do,
    the coefficients then involving the other generators, so that
    kappa(P) = Frac(F[gens]/(p)) is a field over F(other generators) -- the
    setting of Bronstein's parallel Risch, where every normal factor of the
    denominator carries a residue (Theorem 7.5)."""
    g = _const_dir(T, p)
    if g is not None:
        return g
    if T.q is None:
        for g in T.gens:
            if sp.Poly(p, g).degree() >= 1:
                return g
    return None


def _canonical_residue_field(T, f, p, g, delta, verbose=False):
    """Algorithm 2 (the canonical residue, Proposition 7.7) at a normal prime P
    over the irreducible p of a transcendental tower (q = None; f = f[0] a
    scalar), computed in the residue field kappa(P) = Frac(F[gens]/(p)) by
    reduction modulo p in the direction g -- with NO substitution of a root, so
    the place may have non-constant coordinates and delta may exceed 1.  Runs
    the local Hermite reduction f <- f - D(c p^{-k}), c = -mu/(k lambda_P) with
    lambda_P the class of p^{delta-1} D p, until the pole reaches order delta,
    then returns tau = (f p / Dp)|_P in kappa(P) (an expression reduced modulo
    p), or None when a denominator met on the way is not coprime to p."""
    gens = T.gens
    fc = sp.cancel(f[0])
    Dp = T.D(T.scalar(p))[0]
    lam = _mod_p(sp.cancel(p ** (delta - 1) * Dp), p, g)
    if lam is None or _iszero(lam):
        return None
    for _ in range(16):
        k = -_vp(fc, p, gens) - delta
        if k < 0:
            return sp.S(0)
        if k == 0:
            return _mod_p(sp.cancel(fc * p / Dp), p, g)
        mu = _mod_p(sp.cancel(p ** (k + delta) * fc), p, g)
        if mu is None:
            return None
        c = _mod_p(sp.cancel(-mu / (k * lam)), p, g)
        if c is None:
            return None
        fc = sp.cancel(fc - T.D(T.scalar(sp.cancel(c / p ** k)))[0])
        if verbose:
            print(f"      Hermite step at ({p}): order {k + delta} -> "
                  f"subtract D(({c}) * ({p})**(-{k}))")
    return None


def _mod_p(expr, p, g):
    """A rational function of g whose denominator is coprime to p, reduced
    modulo p: a polynomial in g of degree < deg p (an expression).  The
    coefficients are kept as expressions, so other generators and algebraic
    constants may be present.  None if the denominator is not invertible."""
    n, d = sp.fraction(sp.cancel(expr))
    others = [s_ for s_ in sp.sympify(expr).free_symbols | sp.sympify(p).free_symbols if s_ != g]
    if others:                                   # coefficients with other generators: over EX
        Pp = sp.Poly(p, g, domain='EX')
        N = sp.Poly(sp.expand(n), g, domain='EX').rem(Pp)
        D = sp.Poly(sp.expand(d), g, domain='EX').rem(Pp)
    else:                                        # constant coefficients: over their number field
        K = _domain(_coeffs_in([g], [n, d, p]))
        Pp = _polyK(K, p, g)
        N = _polyK(K, n, g).rem(Pp)
        D = _polyK(K, d, g).rem(Pp)
    try:
        Dinv = D.invert(Pp)
    except (sp.polys.polyerrors.NotInvertible, ZeroDivisionError):
        return None
    return sp.expand((N * Dinv).rem(Pp).as_expr())


def _PK(expr, g):
    """Poly in g over the algebraic number field generated by its constants."""
    return sp.Poly(sp.expand(expr), g, extension=True).to_field()


def _polyY_strip(A, pc):
    A = [a.rem(pc) for a in A]
    while A and A[-1].is_zero:
        A.pop()
    return A


def _polyY_rem(A, B, pc):
    """A mod B for polynomials in Y (lists of Poly in g over Kc, low degree
    first) with coefficients in the ring Kc[g]/(pc); raises NotInvertible when
    the leading coefficient of B is a zero divisor there."""
    A, B = _polyY_strip(A, pc), _polyY_strip(B, pc)
    inv = B[-1].invert(pc)
    while len(A) >= len(B):
        cf = (A[-1] * inv).rem(pc)
        sh = len(A) - len(B)
        for i, b in enumerate(B):
            A[sh + i] = (A[sh + i] - cf * b).rem(pc)
        A = _polyY_strip(A, pc)
    return A


def _sheets_over(T, g, pc, taus, c, Kc):
    """The sheets over the prime pc (a Poly in g over Kc) on which the residue
    tau(y) = sum_i taus[i] w_i takes the value c: the gcd G(Y) of Y^m - q and
    c - tau(Y) over the residue ring Kc[g]/(pc).  Returns a list of
    (pc_j, sheet) with sheet the sheet polynomial Y0 (deg G = 1), 'all'
    (deg G = m: every sheet, the divisor over pc_j is principal) or None
    (1 < deg G < m: the places with residue c over a root of pc_j are several
    but not all sheets, which the realisation does not represent).  A zero
    divisor met in the Euclidean algorithm means pc is reducible over Kc: it
    is factored and the sheets are computed over each factor."""
    from sympy.polys.polyerrors import NotInvertible
    m = T.m
    PK = lambda e: _polyK(Kc, e, g)
    try:
        A = [PK(-T.q)] + [PK(0)] * (m - 1) + [PK(1)]
        B = [(PK(-taus[i]) * PK(T.E[i]).invert(pc)).rem(pc) for i in range(m)]
        B[0] = (B[0] + PK(c)).rem(pc)
        A, B = _polyY_strip(A, pc), _polyY_strip(B, pc)
        while B:
            A, B = B, _polyY_rem(A, B, pc)
        G = A
    except NotInvertible:
        facs = [fc for fc, _ in pc.factor_list()[1] if fc.degree() >= 1]
        if len(facs) <= 1:
            return [(pc, None)]
        return [r for fc in facs for r in _sheets_over(T, g, fc.monic(), taus, c, Kc)]
    degG = len(G) - 1
    if degG == 1:
        Y0 = (-(G[0] * G[1].invert(pc))).rem(pc)
        return [(pc, Y0)]
    if degG == m:
        return [(pc, 'all')]
    return [(pc, None)]


def _residue_classes(T, p, tp, Y, verbose=False):
    """Residues at the places over a prime p of ANY degree, computed in the
    residue field K[g]/(p) instead of at explicit roots (the residue-polynomial
    step of Rothstein and Trager inside Algorithm 2 of Part II).

    tp is the residue expression e (f h / Dh) as a tuple; its classes tau_i
    mod p are the coordinates of the residue on the sheets over each root
    alpha of p.  Their minimal polynomial over K is the residue polynomial
        R(z) = res_g(p, N(z - tau)),   N(z - tau) = det(z I - M_tau)
    (for m = 2: (z - tau0)^2 - tau1^2 q; R = res_g(p, z - tau0) when q is
    absent), whose irreducible factors give the residue values c and the
    fields K(c); the places with residue c lie over
        p_c = gcd(p, N(c - tau))
    on the sheet y = Y0(g) with Y0^m = q mod p_c, the root of
    gcd(Y^m - q, c - tau(Y)) over K(c)[g]/(p_c) (for m = 2: Y0 =
    (c - tau0)/tau1); where every sheet carries c the divisor over that
    factor is principal.

    Returns (g, classes, principal): classes = [(c, p_c, Y0)] and
    principal = [(c, p_c2)]; a status tuple ('not elementary', ...) or
    ('failed', ...); or None when p has no usable direction."""
    g = _residue_dir(T, p)
    if g is None:
        return None
    q, m = T.q, T.m
    others = set(T.gens) - {g}
    ncomp = T.n if q is not None else 1
    taus = [_mod_p(tp[i], p, g) for i in range(ncomp)]
    if any(t is None for t in taus):
        return ("failed", "residue not reducible modulo the prime", p)
    if not set().union(*[t.free_symbols for t in taus]).isdisjoint(others):
        # the residue depends on another generator: it is not a constant
        return ("not elementary", p, T.to_Y(tuple(taus) + (sp.S(0),) * (T.n - ncomp), Y))
    tau0 = taus[0]
    tau1 = taus[1] if q is not None and m == 2 else sp.S(0)
    z = sp.Dummy('z')
    charp = None
    if q is None:
        R = sp.resultant(p, sp.expand(z - tau0), g)
    elif m == 2:
        t1q = _mod_p(sp.expand(tau1 ** 2 * q), p, g)
        R = sp.resultant(p, sp.expand((z - tau0) ** 2 - t1q), g)
    else:
        # N(z - tau): the characteristic polynomial of multiplication by tau
        M = T.basis.matrix(tuple(taus))
        charp = sp.expand((z * sp.eye(m) - M).det(method='berkowitz'))
        charp = sp.Add(*[_mod_p(coef, p, g) * z ** k for (k,), coef in sp.Poly(charp, z).terms()])
        R = sp.resultant(p, charp, g)
    R = sp.expand(R)
    if R == 0 or not R.has(z):
        return ("failed", "degenerate residue polynomial", p, R)
    try:
        facs = sp.factor_list(R, z, extension=True)[1]
    except Exception:
        facs = sp.factor_list(R, z)[1]
    if verbose:
        print(f"      residue polynomial over ({p}): "
              f"{' * '.join('(%s)^%d' % (sp.factor(F.as_expr().subs(z, sp.Symbol('z'))), m_) for F, m_ in facs)}")
    values = []
    for F, _m in facs:
        F = sp.Poly(F.as_expr() if hasattr(F, 'as_expr') else F, z)
        if F.degree() < 1:
            continue
        rd = sp.roots(F)
        if sum(rd.values()) != F.degree():
            return ("failed", "residue values not expressible in radicals", p, F.as_expr())
        for c in rd:
            c = sp.radsimp(sp.expand_complex(c)) if not c.free_symbols else c
            if _iszero(c):
                continue
            if not any(_iszero(c - c2) for c2 in values):
                values.append(c)
    Pp = _PK(p, g)
    classes, principal = [], []
    base_consts = []
    if q is not None and m >= 3:
        for t in taus:
            base_consts += sp.Poly(t, g).all_coeffs()
        base_consts += sp.Poly(q, g).all_coeffs() + sp.Poly(p, g).all_coeffs()
        for Ei in T.E:
            base_consts += sp.Poly(Ei, g).all_coeffs()
    for c in values:
        if q is None:
            pc = Pp.gcd(_PK(tau0 - c, g)).monic()
            if pc.degree() >= 1:
                principal.append((c, pc.as_expr()))
            continue
        if m >= 3:
            Kc = _domain([c] + base_consts)
            PK = lambda ex: _polyK(Kc, ex, g)
            pcP = PK(p).gcd(PK(charp.subs(z, c))).monic()
            if pcP.degree() < 1:
                continue
            for pcj, sheet in _sheets_over(T, g, pcP, taus, c, Kc):
                if sheet is None:
                    return ("failed", "residue class on several sheets over one root (m >= 3)", p, c)
                if isinstance(sheet, str):
                    principal.append((c, pcj.as_expr()))
                else:
                    classes.append((c, pcj.as_expr(), sp.expand(sheet.as_expr())))
            continue
        E = _PK(sp.expand(tau1 ** 2 * q - (c - tau0) ** 2), g)
        pc = Pp.gcd(E).monic()
        if pc.degree() < 1:
            continue
        t1 = _PK(tau1, g).rem(pc)
        p2 = pc.gcd(t1).monic()
        if p2.degree() >= 1:
            principal.append((c, p2.as_expr()))
            pc = pc.quo(p2)
        if pc.degree() < 1:
            continue
        Y0 = (_PK(c - tau0, g) * t1.rem(pc).invert(pc)).rem(pc)
        assert (Y0 ** 2 - _PK(q, g)).rem(pc).is_zero
        classes.append((c, pc.as_expr(), sp.expand(Y0.as_expr())))
    if verbose:
        for c, pc, Y0 in classes:
            print(f"      residue class {c}: places over {pc} on the sheet y = {Y0}")
        for c, p2 in principal:
            print(f"      residue {c} on {'both' if m == 2 else 'all'} sheets over {p2}: log({p2})")
    return g, classes, principal


def _realise_class(T, g, supp, c, mmax=12, verbose=False):
    """Realisation of the residue class c supported on the places over the
    primes p_i of supp = [(p_i, Y0_i)], sheet y = Y0_i(g): the logand
    u = a + b y with div(u) = m D_c - n_+ oo_+ - n_- oo_- for the least m <= mmax
    for which one exists, found by LINEAR algebra over K(c): Y0_i is lifted by
    Hensel's iteration to Y_i with Y_i^2 = q mod p_i^m, and 'u vanishes to
    order >= m along D_c' is the linear condition a + b Y_i = 0 mod p_i^m; the
    pole orders (n_+, n_-) at the two places at infinity (deg q even) are
    fixed in turn, so that N(u) = a^2 - q b^2 has degree exactly m deg D_c and
    is a constant times prod p_i^m.  Returns (c/m, (a, b)) or None."""
    from sympy.polys.constructor import construct_domain
    from sympy.polys.matrices import DomainMatrix
    q = T.q
    dq = sp.degree(q, g)
    lc = sp.LC(q, g)
    consts = [c, lc] + [z for pc, Y0 in supp for z in
                        sp.Poly(pc, g).all_coeffs() + sp.Poly(Y0, g).all_coeffs()]
    consts += sp.Poly(q, g).all_coeffs()
    Kc = _domain(consts)
    P = lambda e: _polyK(Kc, e, g)
    Pq = P(q)
    half = P(sp.Rational(1, 2))
    try:
        sqrt_lc = _convK(Kc, sp.sqrt(lc))
    except Exception:
        sqrt_lc = None
    deg_supp = sum(sp.degree(pc, g) for pc, _ in supp)
    lifts = [(P(pc), P(Y0)) for pc, Y0 in supp]
    for m in range(1, mmax + 1):
        mods = []
        for Pc, Yk in lifts:
            M = Pc
            for k in range(1, m):
                M = M * Pc
                Yk = ((Yk + Pq * Yk.invert(M)) * half).rem(M)
            mods.append((M, Yk))
        lifts = [(Pc, Yk) for (Pc, _), (M, Yk) in zip(lifts, mods)]   # keep the lifted sheet for the next m
        n = m * deg_supp
        if dq % 2 == 1:
            configs = [(n // 2, (n - dq) // 2, None)]
        else:
            h1 = dq // 2
            configs = []
            for nplus in range(0, n + 1):
                nminus = n - nplus
                Na = max(nplus, nminus)
                if Na - h1 < 0:
                    continue
                if nplus != nminus and sqrt_lc is None:
                    continue
                configs.append((Na, Na - h1, (nplus, nminus)))
        for Na, Nb, inf in configs:
            if Nb < 0:
                continue
            basis = [(P(g ** j), None) for j in range(Na + 1)] + \
                    [(P(g ** j), 'y') for j in range(Nb + 1)]
            rows = []
            for M, Yk in mods:
                dM = M.degree()
                cols = []
                for B, kind in basis:
                    r = (B if kind is None else B * Yk).rem(M)
                    cs = r.all_coeffs()[::-1]                    # ascending
                    cs = cs + [Kc.zero] * (dM - len(cs))
                    cols.append([Kc.convert(x) for x in cs])
                for i in range(dM):
                    rows.append([col[i] for col in cols])
            if inf is not None and inf[0] != inf[1]:
                nplus, nminus = inf
                eps = Kc.one if nplus < nminus else -Kc.one
                nsmall = min(nplus, nminus)
                # y = eps sqrt(lc) g^h1 S(1/g), S(w) = sqrt(q(1/w) w^(2 h1) / lc)
                w = sp.Dummy('w')
                Sw = sp.series(sp.sqrt(sp.expand(q.subs(g, 1 / w) * w ** (2 * h1) / lc)),
                               w, 0, Na - nsmall + 1).removeO()
                s = [_convK(Kc, sp.nsimplify(sp.expand(Sw).coeff(w, k)))
                     for k in range(Na - nsmall + 1)]
                for e in range(Na, nsmall, -1):
                    row = []
                    for B, kind in basis:
                        j = B.degree()
                        if kind is None:
                            row.append(Kc.one if j == e else Kc.zero)
                        else:
                            k = j + h1 - e
                            row.append(eps * sqrt_lc * s[k] if 0 <= k < len(s) else Kc.zero)
                    rows.append(row)
            if not rows:
                continue
            dm = DomainMatrix(rows, (len(rows), len(basis)), Kc)
            ns = dm.nullspace()
            if ns.shape[0] == 0:
                continue
            vec = ns.to_Matrix().row(0)
            a = sum((vec[j] * g ** j for j in range(Na + 1)), sp.S(0))
            b = sum((vec[Na + 1 + j] * g ** j for j in range(Nb + 1)), sp.S(0))
            a, b = sp.expand(sp.radsimp(a)), sp.expand(sp.radsimp(b))
            # certificate: N(u) is a constant times prod p_i^m (no other zero)
            N = P(a) ** 2 - Pq * P(b) ** 2
            Mall = P(1)
            for M, _ in mods:
                Mall = Mall * M
            quo, rem = N.div(Mall)
            if not rem.is_zero or quo.degree() > 0 or N.is_zero:
                continue
            if verbose:
                print(f"      residue class {c}: div(u) = {m} D_c - ({inf[0]}, {inf[1]}) oo"
                      if inf else f"      residue class {c}: div(u) = {m} D_c - {n} oo",
                      f"; u = {a} + ({b})*y, N(u) = {quo.as_expr()} * ({' * '.join(str(pc) for pc, _ in supp)})^{m}; "
                      f"coefficient {sp.radsimp(c / m)}")
            return (sp.radsimp(c / m), (a, b))
    return None


# ------------------------------------------------------------- pipeline

def _infinity_data(T, g, Kc, lmax):
    """The places over g = oo of y^m = q(g), deg q = d, lc(q) = c, for the
    curve variable g: s = gcd(m, d) places oo_j (j = 0..s-1), each of
    ramification index e = m/s, with local parameter t, g = t^-e and
        y = zeta^j c^(1/m) t^-d' S(t^e),   d' = d/s,   S(u) = (q(1/u) u^d / c)^(1/m),
    so that g^k w_i = zeta^(ij) c^(i/m) t^-v(k,i) F_i(t^e), F_i = S^i / Et_i,
    Et_i(u) = u^deg(E_i) E_i(1/u), v(k,i) = e k + i d' - e deg(E_i) the pole
    order.  Returns (s, e, d', degE, v, coef) with coef(j, k, i, r) the
    coefficient of t^r in the expansion of g^k w_i at oo_j (series to
    order u^lmax; coefficients in the field Kc, which must contain zeta,
    c^(1/m) and the coefficients of q)."""
    q, m = T.q, T.m
    d = sp.degree(q, g)
    lc = sp.LC(q, g)
    s = sp.igcd(m, d)
    e = m // s
    dp = d // s
    u = sp.Dummy('u')
    qt = sp.expand(sp.expand(q.subs(g, 1 / u) * u ** d) / lc)
    S = sp.series(qt ** sp.Rational(1, m), u, 0, lmax + 1).removeO()
    F, degE = [], []
    Spow = sp.S(1)
    for i in range(m):
        Ei = T.E[i]
        dE = sp.degree(Ei, g) if Ei != 1 else 0
        Et = sp.expand(u ** dE * Ei.subs(g, 1 / u))
        Fi = sp.expand(sp.series(Spow / Et, u, 0, lmax + 1).removeO())
        F.append([_convK(Kc, sp.expand(Fi.coeff(u, l))) for l in range(lmax + 1)])
        degE.append(dE)
        Spow = sp.expand(sp.series(Spow * S, u, 0, lmax + 1).removeO())
    zk = _convK(Kc, _zeta(m))
    ck = _convK(Kc, _mroot(lc, m))
    def v(k, i):
        return e * k + i * dp - e * degE[i]
    def coef(j, k, i, r):
        l, rr = divmod(r + v(k, i), e)
        if rr != 0 or l < 0 or l > lmax:
            return Kc.zero
        return zk ** (i * j) * ck ** i * F[i][l]
    return s, e, dp, degE, v, coef


def _find_element(T, g, Kc, affine, zorders, inf):
    """An element u = sum_i a_i(g) w_i of the integral closure O (polynomial
    coordinates over Kc) with
      * u = 0 modulo (M, sheet) for every affine condition (M, [B_0..B_{m-1}])
        of affine, B_i = Y^i / E_i mod M for the Hensel-lifted sheet Y
        (the linear conditions sum_i a_i B_i = 0 mod M), and
      * v_{oo_j}(u) >= zorders[j] at the s places at infinity (a negative
        entry allows a pole of that order, a positive one demands a zero),
    by linear algebra over Kc: the basis g^k w_i is bounded by the largest
    pole allowed (no cancellation of the leading terms can occur at every
    place at once), the conditions at infinity are the vanishing of the
    Laurent coefficients from the expansions of _infinity_data.  When the
    divisor asked for has degree 0 the solution space has dimension <= 1.
    Returns the tuple of coordinates or None."""
    from sympy.polys.matrices import DomainMatrix
    m = T.m
    s, e, dp, degE, v, coef = inf
    Dmax = max([-z for z in zorders] + [0])
    kmax = Dmax // e + max(degE) + 1
    basis = [(k, i) for i in range(m) for k in range(kmax + 1) if v(k, i) <= Dmax]
    if not basis:
        return None
    PK = lambda ex: _polyK(Kc, ex, g)
    rows = []
    for M, Bs in affine:
        dM = M.degree()
        cols = []
        for k, i in basis:
            r = (PK(g ** k) * Bs[i]).rem(M)
            cs = r.all_coeffs()[::-1]
            cs = cs + [Kc.zero] * (dM - len(cs))
            cols.append([Kc.convert(x) for x in cs])
        for t in range(dM):
            rows.append([col[t] for col in cols])
    for j in range(s):
        for r in range(-Dmax, zorders[j]):
            rows.append([coef(j, k, i, r) for k, i in basis])
    if not rows:
        return None
    dm = DomainMatrix(rows, (len(rows), len(basis)), Kc)
    ns = dm.nullspace()
    if ns.shape[0] == 0:
        return None
    vec = ns.to_Matrix().row(0)
    a = [sp.S(0)] * m
    for idx, (k, i) in enumerate(basis):
        a[i] += vec[idx] * g ** k
    return tuple(sp.expand(sp.radsimp(ai)) for ai in a)


def _realise_class_general(T, g, supp, c, mmax=12, verbose=False):
    """Realisation of the residue class c for m >= 3 (the counterpart of
    _realise_class): supp = [(p_i, Y0_i)] lists the primes and sheet
    polynomials (Y0_i^m = q mod p_i) of the places carrying the residue c; the
    logand u in O with div(u) = N D_c - sum_j n_j oo_j is sought for
    N = 1, 2, ..., mmax and every distribution (n_j) of the N deg(D_c) poles
    over the s = gcd(m, deg q) places at infinity, by _find_element with
    the sheets lifted to Y_i^m = q mod p_i^N (Newton) and the condition
    u = 0 mod (p_i^N, Y_i).  The norm N(u) = const * prod p_i^N certifies the
    divisor.  Returns (c/N, u) or None."""
    q, m = T.q, T.m
    d = sp.degree(q, g)
    lc = sp.LC(q, g)
    consts = [c, lc, _zeta(m), _mroot(lc, m)] + sp.Poly(q, g).all_coeffs()
    for pc, Y0 in supp:
        consts += sp.Poly(pc, g).all_coeffs() + sp.Poly(Y0, g).all_coeffs()
    for Ei in T.E:
        consts += sp.Poly(Ei, g).all_coeffs()
    Kc = _domain(consts)
    PK = lambda ex: _polyK(Kc, ex, g)
    Pq = PK(q)
    PE = [PK(Ei) for Ei in T.E]
    deg_supp = sum(sp.degree(pc, g) for pc, _ in supp)
    s = sp.igcd(m, d)
    e = m // s
    lifts = [(PK(pc), PK(pc), PK(Y0).rem(PK(pc))) for pc, Y0 in supp]     # (p_i, p_i^N, Y_i)
    inf, inf_l = None, -1
    for N in range(1, mmax + 1):
        if N > 1:
            new = []
            for Pc, M, Yk in lifts:
                M2 = M * Pc
                Yk = (Yk - (Yk ** m - Pq) * (m * Yk ** (m - 1)).invert(M2)).rem(M2)
                new.append((Pc, M2, Yk))
            lifts = new
        affine = []
        for Pc, M, Yk in lifts:
            Bs = [((Yk ** i) * PE[i].invert(M)).rem(M) for i in range(m)]
            affine.append((M, Bs))
        n = N * deg_supp
        lmax = 2 * n // e + 2
        if inf is None or lmax > inf_l:
            inf = _infinity_data(T, g, Kc, lmax)
            inf_l = lmax
        for cfg in sorted(_compositions(n, s), key=lambda c_: (max(c_), c_)):
            u = _find_element(T, g, Kc, affine, [-nj for nj in cfg], inf)
            if u is None:
                continue
            Nu = PK(T.norm(u))
            Mall = PK(1)
            for _, M, _ in lifts:
                Mall = Mall * M
            quo, rem = Nu.div(Mall)
            if Nu.is_zero or not rem.is_zero or quo.degree() > 0:
                continue
            if verbose:
                print(f"      residue class {c}: div(u) = {N} D_c - {cfg} oo; "
                      f"u = {T.to_Y(u, sp.Symbol('y'))}, N(u) = {quo.as_expr()} * "
                      f"({' * '.join(str(pc) for pc, _ in supp)})^{N}; coefficient {sp.radsimp(c / N)}")
            return (sp.radsimp(c / N), u)
    return None


def _realise_class_any(T, g, supp, c, mmax=12, verbose=False):
    if T.m == 2:
        return _realise_class(T, g, supp, c, mmax=mmax, verbose=verbose)
    return _realise_class_general(T, g, supp, c, mmax=mmax, verbose=verbose)


def _in_lattice(z, basis, bound):
    """Is the integer vector z a Z-combination of the basis vectors with
    coefficients of absolute value <= bound (a product of powers of units
    already found)?"""
    if not basis:
        return False
    for cs in _iproduct(*[range(-bound, bound + 1)] * len(basis)):
        if all(sum(c_ * b[j] for c_, b in zip(cs, basis)) == z[j] for j in range(len(z))):
            return True
    return False


def _units_general(T, g, B=None, verbose=False):
    """Unit candidates of O for m >= 3 (Algorithm 4, Step 6; the continued
    fraction of Part I is m = 2 only): the units are the elements whose
    divisor sum_j z_j oo_j is supported at the s = gcd(m, deg q) places at
    infinity, sum_j z_j = 0.  Every such divisor of degree (sum of the
    positive z_j) <= B is tried by _find_element; the search is a bounded
    height search and is not complete (no non-torsion certificate for
    m >= 3).  For s = 1 there are no non-constant units.  Returns the list
    of unit tuples found (multiples of a found divisor are skipped)."""
    q, m = T.q, T.m
    d = sp.degree(q, g)
    lc = sp.LC(q, g)
    s = sp.igcd(m, d)
    if s == 1:
        return []
    e = m // s
    if B is None:
        B = 4 if s <= 3 else 3
    consts = [lc, _zeta(m), _mroot(lc, m)] + sp.Poly(q, g).all_coeffs()
    for Ei in T.E:
        consts += sp.Poly(Ei, g).all_coeffs()
    Kc = _domain(consts)
    PK = lambda ex: _polyK(Kc, ex, g)
    inf = _infinity_data(T, g, Kc, 2 * B // e + 2)
    found = []
    for deg in range(1, B + 1):
        for pos in _compositions(deg, s):
            for neg in _compositions(deg, s):
                if any(pj and nj for pj, nj in zip(pos, neg)):
                    continue
                z = [pj - nj for pj, nj in zip(pos, neg)]
                if _in_lattice(z, [zf for zf, _ in found], deg):
                    continue
                u = _find_element(T, g, Kc, [], z, inf)
                if u is None:
                    continue
                Nu = PK(T.norm(u))
                if Nu.is_zero or Nu.degree() != 0:
                    continue
                found.append((z, u))
                if verbose:
                    print(f"  unit candidate (m = {m}): {T.to_Y(u, sp.Symbol('y'))} with "
                          f"divisor {z} on the {s} places at infinity, N(u) = {Nu.as_expr()}")
    return [u for _, u in found]


def _realise_at_points(T, p, pts, taus, verbose=False):
    """m >= 3, explicit places with constant coordinates over p: the residue
    classes are the distinct nonzero values c, each supported on the places
    (rho, y0) with residue c, i.e. the primes g - rho with the constant sheet
    y0; realised by _realise_class_general.  Returns [(coeff, u)] or None."""
    g = pts[0][0]
    if any(sp.sympify(rho).free_symbols or sp.sympify(yv).free_symbols for _, rho, yv in pts):
        return None
    groups = []
    for pt, tt in zip(pts, taus):
        if _iszero(tt):
            continue
        for grp in groups:
            if _iszero(grp[0] - tt):
                grp[1].append(pt)
                break
        else:
            groups.append((tt, [pt]))
    out = []
    for c, gpts in groups:
        supp = [(sp.expand(g - rho), yv) for _, rho, yv in gpts]
        got = _realise_class_general(T, g, supp, c, verbose=verbose)
        if got is None:
            return None
        out.append(got)
    return out


def parallel_integrate_mixed(f, T, bounds=None, extension=None, verbose=False,
                             split_specials=False, special_exp=0, model_changed=False,
                             split_first=False):
    """Retry sequence (each a guessed input or a change of model):
       1. the base run with the tower specials over Q (and the exponent retries
          inside _pim);
       2. a conic radicand with a rational point is parametrised away BEFORE
          any work over the algebraic closure;
       3. specials split over Fbar;
       4. a quartic radicand is moved to its cubic model.
    split_first=True (an experiment, off by default) allows step 3 already in
    the base run of a conic tower, i.e. before the parametrisation.
    Steps 2 and 4 are changes of model of a curve y^2 = q and apply to m = 2
    only."""
    def failed(r_):
        return isinstance(r_, tuple) and r_[0] in (
            "failed", "needs torsion realisation (Parts I--II, milestone iii)")
    # a single generator g over the curve with Dg = r(g) != 1 -- a flattened
    # root (Lemma 3.2) or the parameter of a parametrised conic -- is rescaled
    # to d/dg (Lemma 3.4): int f dx = int (f/r) dg with the same antiderivative,
    # and the tower is the setting of Part I (exact bounds, Prop. 9.2(b))
    if len(T.gens) == 1 and T.q is not None:
        g0, d0 = T.gens[0], T.derivs[0]
        r0 = d0[0]
        if r0 != 1 and all(c == 0 for c in d0[1:]) and r0.free_symbols <= {g0}:
            if verbose:
                print(f"  single generator {g0} with D{g0} = {r0}: rescaled to d/d{g0} (Lemma 3.4)")
            T = Tower([g0], [(sp.S(1),)], T.q, T.m)
            f = tuple(sp.cancel(c / r0) for c in f)
    if not model_changed:
        _FIELDS.clear(); _CONVS.clear()          # the number fields are those of this integrand
    gq = [g for g in T.gens if T.q is not None and T.q.free_symbols <= {g}]
    const_q = bool(gq) and all(c.free_symbols == set() for c in sp.Poly(T.q, gq[0]).all_coeffs())
    is_conic = T.m == 2 and const_q and sp.degree(T.q, gq[0]) == 2
    is_quartic = (T.m == 2 and const_q and sp.degree(T.q, gq[0]) == 4
                  and sp.sqrt(sp.LC(T.q, gq[0])).is_rational)    # two rational places at infinity
    r = _pim(f, T, bounds, extension, verbose, split_specials, special_exp, model_changed,
             allow_split=split_first or not (is_conic and not model_changed))
    if not model_changed and failed(r) and bounds is None:
        if is_conic:
            res = conic_to_line(T, f)
            if res is not None:
                T2, f2, back = res
                if verbose:
                    print(f"  conic radicand: parametrised by {back[0][0]} = {back[0][1]}; "
                          f"the tower is now transcendental over Q({back[0][0]})")
                r2 = parallel_integrate_mixed(f2, T2, bounds=None, extension=extension, verbose=verbose,
                                              model_changed=True)
                if isinstance(r2, sp.Basic):
                    return r2.subs(back)
                if r2[0] == "not elementary":
                    return r2
            # no rational point, or the parametrised run failed: allow the split now
            r = _pim(f, T, bounds, extension, verbose, split_specials, special_exp, model_changed,
                     allow_split=True)
        if failed(r) and is_quartic:
            try:
                T2, f2, back = quartic_to_cubic(T, f)
            except Exception:
                return r
            if verbose:
                print(f"  quartic radicand: changing to the cubic model y^2 = {T2.q} "
                      f"(s = {back[1][1]})")
            r2 = parallel_integrate_mixed(f2, T2, bounds=None, extension=extension, verbose=verbose,
                                          model_changed=True)
            if isinstance(r2, sp.Basic):
                return r2.subs(back)
            return r2 if r2[0] == "not elementary" else r
    return r


class _Analysis:
    """Steps 1--14 of Algorithm 4 for one integrand over one tower: the
    classification, the residues and their realisation, the tower specials,
    the units and the residual, computed once by _analyse and reused by every
    rung of the retry ladder (special exponents, exact bounds, the split of
    the specials over Fbar), which only re-enters at Step 15 (_solve_stage).
    The specials over Fbar and the S'-units over them (Steps 5--6 for the
    split variant) and the columns D u / u of the logands are memoised."""
    def __init__(self, T, f, Y, det_logs, unk_logs, denv, units, units_complete, rem, verbose):
        self.T, self.f, self.Y, self.verbose = T, f, Y, verbose
        self.det_logs, self.unk_logs, self.denv = det_logs, unk_logs, denv
        self.units, self.units_complete, self.rem = units, units_complete, rem
        self._specials, self._cols = {}, {}

    def specials(self, split):
        """(unk_logs, special_units) for the specials over Q (split=False) or
        over Fbar (split=True): the special logands and the S'-units found over
        them, computed once per variant."""
        if split in self._specials:
            return self._specials[split]
        T, verbose = self.T, self.verbose
        gens, q, m = T.gens, T.q, T.m
        unk_logs = list(self.unk_logs)
        # specials over Fbar (Theorem 6.1): on request, replace each special
        # p(g) with constant coefficients by its linear factors g - r
        if split:
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

        # S'-units split over a special prime (Algorithm 4, Step 6: generators
        # of O_{S'}^*): u = a + b y with N(u) = c p^k for a special p, found by
        # the norm search; e.g. 1 +- sqrt(1 - x^2) over the special x of log x
        # (m = 2 only: for m >= 3 the S'-units over specials are not searched)
        special_units = []
        if q is not None and m == 2:
            for pp, _ in unk_logs:
                for g in gens:
                    if (q.free_symbols <= {g} and sp.Poly(pp, g).degree() >= 1
                            and all(c_.free_symbols.isdisjoint(set(gens))
                                    for c_ in sp.Poly(pp, g).all_coeffs())):
                        # generators, not the whole group: constant b first, then
                        # rational coefficients before algebraic ones, at most
                        # four per special (their products span the rest)
                        sols = [s_ for s_ in _norm_search_all(q, pp, g, kmax=2, dbmax=1) if s_[1] != 0]
                        sols.sort(key=lambda s_: (sp.degree(s_[1], g),
                                                  0 if all(z.is_rational for z in
                                                           sp.Poly(s_[0], g).all_coeffs() +
                                                           sp.Poly(s_[1], g).all_coeffs()) else 1,
                                                  s_[3]))
                        n_here = 0                        # the cap is per special, not global
                        for a, b, c, k in sols:
                            if n_here >= 4:
                                break
                            for sg in (1, -1):
                                uu = (sp.expand(a), sp.expand(sg * b))
                                if uu not in special_units and (-uu[0], -uu[1]) not in special_units:
                                    special_units.append(uu)
                                    n_here += 1
                                    if verbose:
                                        print(f"  S'-unit over special ({pp}): "
                                              f"{uu[0]} + ({uu[1]})*y  (N = {c}*({pp})**{k})")
                        # torsion classes of the places over p (cubic models):
                        # the Miller functions are S'-units too
                        if sp.degree(q, g) == 3:
                            pts_s = _points_over(T, pp)
                            if pts_s is not None and all(
                                    sp.sympify(pt[1]).free_symbols.isdisjoint(set(gens)) and
                                    sp.sympify(pt[2]).free_symbols.isdisjoint(set(gens)) for pt in pts_s):
                                Ys = sp.Dummy('y')
                                for pt in pts_s:
                                    if len(special_units) >= 8:
                                        break
                                    res_ = _torsion_order_and_miller(q, g, pt, Ys)
                                    if res_ is None:
                                        continue
                                    m_, uu = res_
                                    if uu not in special_units:
                                        special_units.append(uu)
                                        if verbose:
                                            print(f"  S'-unit over special ({pp}): Miller function of "
                                                  f"[P - oo] of order {m_} at ({pt[1]}, {pt[2]})")
                        break
        elif q is not None and unk_logs and verbose:
            print(f"  S'-units over the specials are not searched for m = {m}")

        self._specials[split] = (unk_logs, special_units)
        return self._specials[split]

    def column(self, kind, u):
        """The column D u / u of a unit or S'-unit (kind 'u', u a tuple) or of a
        special logand (kind 's', u a polynomial), with its coordinates as
        cancelled (numerator, denominator) pairs; computed once per logand."""
        key = (kind, tuple(u) if kind == 'u' else u)
        if key not in self._cols:
            T, q = self.T, self.T.q
            nc = T.n if q is not None else 1
            if kind == 'u':
                col = T.div(T.D(u), u)
            else:
                col = (T.div(T.D(T.scalar(u)), T.scalar(u)) if q is not None
                       else (sp.cancel(T.D((u, sp.S(0)))[0] / u), sp.S(0)))
            self._cols[key] = (col, [sp.fraction(_c(col[i])) for i in range(nc)])
        return self._cols[key]


def _analyse(f, T, extension=None, verbose=False):
    """Steps 1--14 of Algorithm 4: returns an _Analysis, or a status tuple
    ('not elementary', ...) / ('failed', ...) / ('needs torsion realisation',
    ...) when the pipeline exits before the ansatz."""
    _cls = {}
    def classify(p):                          # Algorithm 1, once per prime
        if p not in _cls:
            _cls[p] = _classify(T, p)
        return _cls[p]
    gens, q, m = T.gens, T.q, T.m
    nc = T.n if q is not None else 1            # coordinates carrying the integrand
    Y = sp.Dummy('y')
    f = T._pad(tuple(f))
    # the integrand must be a rational function of the generators: an opaque
    # function such as atan(x) would be treated as a constant by the linear
    # solver and produce a wrong integral
    for comp in f[:nc]:
        cc = sp.cancel(sp.sympify(comp))
        n_, d_ = sp.fraction(cc)
        bad = (not n_.is_polynomial(*gens) or not d_.is_polynomial(*gens)
               or any(not a.free_symbols.isdisjoint(set(gens))
                      for a in cc.atoms(sp.Function)))
        if bad:
            raise ValueError(f"integrand component {comp} is not a rational "
                             "function of the generators; build the tower first")
    f = tuple(sp.cancel(f[i]) if i < nc else sp.S(0) for i in range(T.n))
    d = sp.S(1)
    for i in range(nc):
        d = sp.lcm(d, sp.fraction(f[i])[1])
    det_logs, unk_logs, denv, torsion = [], [], sp.S(1), []
    pending_classes = []                       # residue classes not realised over their own prime

    fl = (sp.factor_list(d, extension=extension)[1] if extension is not None
          else sp.factor_list(sp.Poly(d, *gens))[1])
    for P_, mult in fl:
        p = P_ if not hasattr(P_, 'as_expr') else P_.as_expr()
        if not any(p.has(g) for g in gens):
            continue
        branch, eta, delta, special = classify(p)
        e_P = m if branch else 1
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
            if q is None and not branch:
                # transcendental tower (pmint's setting): the canonical residue
                # at any pole order, computed in kappa(P) with no root
                # substitution, so the place may have non-constant coordinates
                # and delta may exceed 1 (Proposition 7.7, general case)
                g_dir = _residue_dir(T, p)
                tau = (_canonical_residue_field(T, f, p, g_dir, delta, verbose)
                       if g_dir is not None else None)
                if tau is not None and not _iszero(tau):
                    if verbose:
                        print(f"      canonical residue at order {-vP}: {tau}")
                    cv = _certify_nonconstant(tau, gens)
                    if cv is True:
                        return ("not elementary", p, tau)
                    if cv is None:
                        return ("failed", "residue constancy undecided", p, tau)
                    det_logs.append((tau, T.scalar(p)))     # log(p), coefficient tau
            elif delta == 1 and not branch:
                pts = _points_over(T, p)
                if pts and q is not None and len(gens) == 1 and T.derivs[0] == T.unit(0):
                    taus = _deep_residues(T, f, p, pts, Y)        # Laurent shortcut (n = 1, D = d/dx)
                elif pts:
                    taus = _canonical_residues(T, f, p, pts, Y, verbose)   # Algorithm 2 as written
                else:
                    taus = None
                if taus is not None:
                    if verbose:
                        print(f"      canonical residues at order {-vP}: {taus}")
                    cert = [(_certify_nonconstant(tt, gens), tt) for tt in taus]
                    if any(cv is True for cv, _ in cert):
                        return ("not elementary", p,
                                [tt for cv, tt in cert if cv is True][0])
                    if any(cv is None for cv, _ in cert):
                        return ("failed", "residue constancy undecided", p,
                                [tt for cv, tt in cert if cv is None][0])
                    if m == 2 or q is None:
                        got = _realise_points(T, p, pts, taus, Y, verbose)
                    else:
                        got = _realise_at_points(T, p, pts, taus, verbose)
                    if got is None:
                        torsion.append((p, pts, taus))
                    else:
                        det_logs.extend(got)
        if vP == -delta:
            # tau_P = e * (f h / Dh)|_P  with h = p
            Dp = T.D(T.scalar(p))
            tp = T.div(_pscale(e_P * p, f), Dp) if q is not None else \
                 (sp.cancel(e_P * p * f[0] / Dp[0]), sp.S(0))
            texpr = T.to_Y(tp, Y)
            if branch:
                raise NotImplementedError("critical branch residue")
            pts = _points_over(T, p)
            # a prime of degree > 4, and every constant-coefficient prime when
            # m >= 3: residues in the residue field K[g]/(p) (no roots), the
            # residue classes as (prime, sheet polynomial), each realised by
            # Hensel lifting and linear algebra over K(c)
            if pts is None or (m >= 3 and _const_dir(T, p) is not None):
                rc = _residue_classes(T, p, tp, Y, verbose)
                if rc is None:
                    raise NotImplementedError(f"residues over ({p}): no "
                                              "constant-coefficient direction")
                if isinstance(rc, tuple) and isinstance(rc[0], str):
                    if not (pts is not None and rc[0] == "failed" and "several sheets" in rc[1]):
                        return rc
                    # fall through to the explicit places
                else:
                    g_dir, classes, principal = rc
                    for cval, pc2 in principal:
                        det_logs.append((cval, T.scalar(pc2)))
                    for cval, pc1, Y0 in classes:
                        got = _realise_class_any(T, g_dir, [(pc1, Y0)], cval, verbose=verbose)
                        if got is None:
                            pending_classes.append((cval, g_dir, pc1, Y0))
                        else:
                            det_logs.append(got)
                    continue
            taus = [_resfmt(_reduce_at(texpr, pt, Y)) for pt in pts]
            if any(sp.sympify(t).has(sp.zoo, sp.nan) for t in taus):
                return ("failed", "residue undefined at the place", p)
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
                    det_logs.append((taus[0], T.scalar(p)))
                continue
            if q is not None and m >= 3:
                got = _realise_at_points(T, p, pts, taus, verbose)
                if got is None:
                    torsion.append((p, pts, taus))
                else:
                    det_logs.extend(got)
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
            torsion.append((p, pts, taus))

    if pending_classes:
        # a residue class may be supported over several primes (as in A28 of
        # the Charlwood suite): realise the classes with equal value jointly
        groups = []
        for cval, g_dir, pc1, Y0 in pending_classes:
            for grp in groups:
                if grp[1] == g_dir and _iszero(grp[0] - cval):
                    grp[2].append((pc1, Y0))
                    break
            else:
                groups.append((cval, g_dir, [(pc1, Y0)]))
        unrealised = []
        for cval, g_dir, supp in groups:
            got = _realise_class_any(T, g_dir, supp, cval, verbose=verbose) if len(supp) > 1 else None
            if got is None:
                unrealised.append((sp.Mul(*[pc for pc, _ in supp]), [cval]))
            else:
                det_logs.append(got)
        if unrealised:
            return ("needs torsion realisation (Parts I--II, milestone iii)", unrealised)
    if torsion and m == 2:
        # the divisor may be realisable only jointly over several primes:
        # by torsion on a cubic model (Algorithm 3(d)), else by the norm
        # search over the product of the primes
        got = _torsion_realise(T, torsion, Y, verbose=verbose)
        if got is None:
            got = _realise_joint(T, torsion, Y, verbose)
        if got is not None:
            det_logs.extend(got)
            torsion = []
    if torsion:
        return ("needs torsion realisation (Parts I--II, milestone iii)",
                [(p, taus) for p, _, taus in torsion])

    # residue at the hypertangent place at infinity (Lemma 8.1)
    if q is not None and len(gens) >= 2:
        tinf = _vinfty_residue(T, f, Y)
        if tinf is not None:
            if verbose:
                print(f"  v_oo (hypertangent top): delta = 1, v_oo(f) = -1, "
                      f"residue {T.to_Y(tinf, sp.Symbol('y'))}")
            lower = [g for g in gens[:-1]]
            nonconst = any(_c(c) != 0 for c in tinf[1:]) or (_certify_nonconstant(tinf[0], lower) is True)
            if nonconst:
                return ("not elementary", "v_oo", tinf)

    # tower specials (Theorem 6.1): offered regardless of the integrand
    seen = {pp for pp, _ in unk_logs}
    cand = set()
    for dpair in list(T.derivs) + (list(T.Dw[1:]) if q is not None else []):
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
        if classify(pp)[3]:
            unk_logs.append((pp, sp.S(0)))
            seen.add(pp)
            if verbose:
                print(f"  tower special: candidate log({pp})")

    # residue-invisible unit candidates (Remark 7.7): m = 2 by the continued
    # fraction of sqrt(q) (pell), m >= 3 by the bounded divisor search at the
    # places at infinity (_units_general)
    units, units_complete = [], True
    if q is not None:
        for g in gens:
            if not q.free_symbols <= {g}:
                continue
            if m == 2 and sp.degree(q, g) % 2 == 0:
                uu = fundamental_unit(q, g)
                if uu is not None:
                    units.append(((uu[0], uu[1]), uu[2]))
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
            elif m >= 3 and all(c_.free_symbols == set() for c_ in sp.Poly(q, g).all_coeffs()):
                for uu in _units_general(T, g, verbose=verbose):
                    units.append((uu, None))
                units_complete = sp.igcd(m, sp.degree(q, g)) == 1
            break

    # residual integrand
    rem = f
    for tau, u in det_logs:
        ld = (T.div(T.D(u), u) if q is not None
              else (sp.cancel(T.D(u)[0] / u[0]), sp.S(0)))
        rem = _padd(rem, _pscale(-tau, ld))

    return _Analysis(T, f, Y, det_logs, unk_logs, denv, units, units_complete, rem, verbose)


def _solve_stage(A, split, special_exp, bounds, verbose):
    """Steps 15--20 of Algorithm 4 for one rung of the ladder: the special
    s-part with the guessed exponent, the ansatz, the linear system
    (Algorithm 5) and the integral.  Returns the integral, or
    ('nosol', bounds) when the system has no solution."""
    T, f, Y = A.T, A.f, A.Y
    gens, q, m = T.gens, T.q, T.m
    nc = T.n if q is not None else 1
    det_logs, denv, units, rem = A.det_logs, A.denv, A.units, A.rem
    unk_logs, special_units = A.specials(split)
    # special s-part: the exponents of tower specials absent from the
    # integrand's denominator are a guessed input (Remark 9.1); on failure
    # the caller retries with special_exp = 1, 2
    if special_exp:
        # raised for every tower special, present in the denominator or not:
        # the multiplicity of a special in D_v is not bounded by its
        # multiplicity in the integrand (there is no valuation lemma there)
        for pp, _ in unk_logs:
            denv *= pp ** special_exp
        if verbose:
            print(f"  special s-part with exponent {special_exp}: D_v = {denv}")

    # ansatz
    if bounds is None:
        nb = [sp.Poly(sp.fraction(rem[i])[0], *gens) for i in range(nc)]
        db = [sp.Poly(sp.fraction(rem[i])[1] * denv, *gens) for i in range(nc)]
        bounds = [max([P.degree(g) for P in nb + db]) + 2 for g in gens]
    prefixes = ['a_', 'b_'] if nc <= 2 else ['c%d_' % i for i in range(nc)]
    css = [[] for _ in range(nc)]
    monos, alphas = [], []
    for alpha in _iproduct(*[range(b + 1) for b in bounds]):
        alphas.append(alpha)
        monos.append(sp.Mul(*[g ** a for g, a in zip(gens, alpha)]))
        for i in range(nc):
            css[i].append(sp.Symbol(prefixes[i] + '_'.join(map(str, alpha))))
    # the system is linear in the unknowns: every basis element of the ansatz
    # (a monomial over D_v, a unit or S'-unit logand, a special logand)
    # contributes a tuple of rational functions FREE of unknowns, computed and
    # cancelled once; the coordinates are then brought over a common
    # denominator by polynomial arithmetic on these unknown-free pieces, and
    # the unknowns enter only as scalar multipliers of polynomial numerators.
    # No together/cancel is ever run on an expression containing unknowns (a
    # multivariate gcd in which the unknowns count as variables is
    # catastrophic over an algebraic extension).  The assembly and the solve
    # run over ONE number field K (_assemble_field, _FieldSystem); the Expr
    # route (_assemble_expr + linsolve) is kept for a constant that is not an
    # algebraic number.
    units = units + [(uu, None) for uu in special_units]
    gammas = [sp.Symbol('gamma_%d' % i) for i in range(len(units))]
    betas = [sp.Symbol('beta_%d' % i) for i in range(len(unk_logs))]
    unks = [c_ for cs_ in css for c_ in cs_] + gammas + betas
    ncoef = sum(len(cs_) for cs_ in css)
    cols = ([(gm, A.column('u', u)) for gm, (u, c) in zip(gammas, units)]
            + [(bt, A.column('s', s)) for bt, (s, _) in zip(betas, unk_logs)])
    try:
        sysK = _assemble_field(T, rem, denv, cols, css, alphas, unks)
        eqs, neq = None, sysK.A.shape[0]
    except _NonAlgebraic:
        sysK = None
        eqs = _assemble_expr(T, rem, denv, cols, css, monos)
        neq = len(eqs)
    if verbose:
        print(f"  ansatz: bounds {bounds}, {len(unks)} unknowns "
              f"({ncoef} coefficients, {len(gammas)} unit/S'-unit logs, "
              f"{len(betas)} special logs), {neq} equations")
    import time as _time
    _t0 = _time.time()
    if sysK is not None:
        sub = sysK.solve()
    else:
        sol = sp.linsolve(eqs, unks)
        sub = None
        if sol:
            sub = dict(zip(unks, list(sol)[0]))
            frees = set().union(*[sp.sympify(v).free_symbols
                                  for v in sub.values()]) & set(unks)
            sub = {k: sp.sympify(v).subs({fp: 0 for fp in frees})
                   for k, v in sub.items()}
    if verbose:
        print(f"  linsolve: {_time.time() - _t0:.1f}s, {'no solution' if sub is None else 'solved'}")
    if sub is None:
        return ('nosol', bounds)
    if sysK is not None:
        rat = sysK.rational_part()                   # cancelled in K[gens]
    else:
        assert all(_algzero(eq.subs(sub)) for eq in eqs)      # the linear equations, exactly
        V = tuple(sp.Add(*[ci * mo for ci, mo in zip(css[i], monos)]) / denv for i in range(nc))
        rat = tuple(sp.cancel(V[i].subs(sub)) for i in range(nc))

    y = sp.Pow(q, sp.Rational(1, m)) if q is not None else None
    def _surf(u):
        if q is None:
            return u[0]
        return sp.Add(*[u[i] * y ** i / T.E[i] for i in range(T.n)])
    I = (_surf(rat)
         + sum(tau * sp.log(_surf(u)) for tau, u in det_logs)
         + sum(sub[g] * sp.log(_surf(u))
               for g, (u, c) in zip(gammas, units))
         + sum(sub[b] * sp.log(s) for b, (s, _) in zip(betas, unk_logs)))
    return I


def _pim(f, T, bounds=None, extension=None, verbose=False,
         split_specials=False, special_exp=0, model_changed=False, allow_split=True,
         analysis=None):
    """f = (f_0, ..., f_{m-1}) <-> sum_i f_i w_i (a pair f0 + f1 y for m <= 2).
    Returns a sympy expression, or a status tuple ('not elementary', ...) /
    ('needs torsion realisation', ...) / ('failed', ...).  The analysis
    (Steps 1--14) is computed once per integrand and tower and cached on the
    tower; the rungs of the retry ladder re-enter at Step 15."""
    A = analysis
    if A is None:
        cache = T.__dict__.setdefault('_analyses', {})
        key = (tuple(sp.sympify(c) for c in f), extension)
        A = cache.get(key)
        if A is None:
            A = _analyse(f, T, extension, verbose)
            if isinstance(A, tuple):
                return A
            cache[key] = A
    gens, q, m = T.gens, T.q, T.m
    bounds_given = bounds
    r = _solve_stage(A, split_specials, special_exp, bounds, verbose)
    if not (isinstance(r, tuple) and r[0] == 'nosol'):
        return r
    bounds = r[1]
    f, Y, rem, units_complete = A.f, A.Y, A.rem, A.units_complete
    unk_logs = A.specials(split_specials)[0]
    g0 = gens[0]
    if (bounds_given is None and _HAVE_RN and q is not None and m == 2 and len(gens) == 1
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
        r2 = _pim(f, T, bounds=[max(B)], verbose=False, model_changed=model_changed, analysis=A)
        if isinstance(r2, tuple) and r2[0] == "failed":
            return ("not elementary", "holomorphic remainder: residual "
                    "second-kind differential is not exact "
                    "(exact bounds of Part I)", B)
        return r2
    if special_exp < 2 and bounds_given is None and unk_logs:
        return _pim(f, T, bounds=None, extension=extension,
                    verbose=verbose, split_specials=split_specials,
                    special_exp=special_exp + 1, model_changed=model_changed,
                    allow_split=allow_split, analysis=A)
    if allow_split and not split_specials and any(
            sp.Poly(pp, g).degree() >= 2 for pp, _ in unk_logs for g in gens
            if sp.Poly(pp, g).degree() >= 0):
        return _pim(f, T, bounds=bounds_given, extension=extension,
                    verbose=verbose, split_specials=True, model_changed=model_changed,
                    allow_split=allow_split, analysis=A)
    return ("failed", "no solution within bounds", bounds)
