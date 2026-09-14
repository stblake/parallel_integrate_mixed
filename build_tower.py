"""build_tower.py -- automatic tower construction for parallel_mixed.py, the
Python counterpart of BuildTower in ParallelMixed.wl.

    integrate_surface(expr, x)   ->  the integral of expr dx, or a certificate /
                                     failure tuple, in terms of x
    build_tower(expr, x)         ->  (Tower, pair, back)

Processing is innermost-first until the integrand is a rational function of
the generators and y:
  * log(a) -> generator t with D t = D a / a; atan, atanh likewise (primitives);
    asin, acos, asinh, acosh -> primitives through the radical y^2 = 1 -+ a^2,
    which becomes the tower's radical if none exists;
  * exp(a) -> t D a; tan, cot, tanh, coth -> (1 +- t^2) D a;
  * sin, cos, sec, csc (and hyperbolic) of one argument are handled as a family
    through a tangent, never an exponential: parity rules first (odd in sin ->
    integration variable u = cos x; odd in cos -> u = sin x), then t = tan a for
    integrands even in (sin, cos), else the half-angle t = tan(a/2);
  * a root base^(k/m) whose base is c g + r with g a generator, c a constant and
    r free of g is flattened (Lemma 3.2): g -> (u^m - r)/c, D u = D base/(m u^(m-1));
    any other root base^(k/m) is the radical y^m = base (bases are normalised
    so that the radicand is an m-th-power-free polynomial; m = 2 gives the
    pair representation on (1, y), m >= 3 the Trager basis w_i = y^i/E_i);
  * a second radical demanded of a conic y^2 = a g^2 + b g + c with a square a
    is removed by the Euler parametrisation y = alpha g + w.
"""
import sympy as sp
from parallel_mixed import Tower, parallel_integrate_mixed, _pair_reduce, _c

GEN_HEADS = (sp.log, sp.exp, sp.tan, sp.cot, sp.tanh, sp.coth,
             sp.atan, sp.acot, sp.atanh, sp.acoth,
             sp.asin, sp.acos, sp.asinh, sp.acosh, sp.asec, sp.acsc, sp.asech, sp.acsch)
# inverse functions with a rational derivative:  D t = coef(a) D a
INV_RATIONAL = {sp.atan: lambda a: 1 / (1 + a ** 2), sp.acot: lambda a: -1 / (1 + a ** 2),
                sp.atanh: lambda a: 1 / (1 - a ** 2), sp.acoth: lambda a: 1 / (1 - a ** 2)}
# inverse functions with a derivative through a radical:  D t = coef(a) D a / sqrt(rad(a));
# the third entry marks a derivative with |a|, whose sign the sample point decides
INV_RADICAL = {sp.asin: (lambda a: 1 - a ** 2, lambda a: 1, False),
               sp.acos: (lambda a: 1 - a ** 2, lambda a: -1, False),
               sp.asinh: (lambda a: 1 + a ** 2, lambda a: 1, False),
               sp.acosh: (lambda a: a ** 2 - 1, lambda a: 1, False),
               sp.asec: (lambda a: a ** 2 - 1, lambda a: 1 / a, True),
               sp.acsc: (lambda a: a ** 2 - 1, lambda a: -1 / a, True),
               sp.asech: (lambda a: 1 - a ** 2, lambda a: -1 / a, False),
               sp.acsch: (lambda a: 1 + a ** 2, lambda a: -1 / a, True)}
TRIG = (sp.sin, sp.cos, sp.sec, sp.csc)
HYP = (sp.sinh, sp.cosh, sp.sech, sp.csch)


class TowerError(Exception):
    pass


def _rational_in(e, vars_):
    e = sp.together(sp.sympify(e))
    n, d = sp.fraction(e)
    return n.is_polynomial(*vars_) and d.is_polynomial(*vars_)


def _rad_rules(e, q, Y, m=2):
    """every power q^(k/m') of the radicand with m' | m -> the radical symbol Y,
    Y^m = q: q^(k/m') = Y^(k m/m') (for m = 2 in the reduced form q^k Y)"""
    if q is None:
        return e
    if m == 2:
        return e.replace(lambda z: isinstance(z, sp.Pow) and z.exp.is_Rational and z.exp.q == 2
                         and sp.expand(z.base - q) == 0,
                         lambda z: q ** (z.exp - sp.Rational(1, 2)) * Y)
    return e.replace(lambda z: isinstance(z, sp.Pow) and z.exp.is_Rational and not z.exp.is_Integer
                     and m % z.exp.q == 0 and sp.expand(z.base - q) == 0,
                     lambda z: Y ** int(z.exp * m))


def _sign_fix(sq, sample):
    """sqrt(sq^2) = |sq|: return sq with the sign it has at the sample point
    (a point where the integrand is real), so that the formal identity
    sqrt(sq^2 sf) = sq sqrt(sf) holds on the integrand's domain."""
    if not sample:
        return sq
    try:
        v = complex(sp.N(sq.subs(sample)))
        if abs(v.imag) < 1e-12 * max(1.0, abs(v.real)) and v.real < 0:
            return -sq
    except (TypeError, ValueError):
        pass
    return sq


def _root_normalize(pw, vars_, sample=None):
    """Pow(base, k/m) with a rational-function base num/den, or a polynomial base
    with m-th-power factors: num den^(m-1) = sq^m sf with sf m-th-power-free,
    base^(k/m) = sq^k sf^(k/m) / den^k, the signs of sq and den chosen at the
    sample point so that the identity holds for the principal branches
    (sqrt(N/D) = sqrt(N D)/|D|; for odd m, (sq^m sf)^(1/m) = sq sf^(1/m) needs
    sq > 0, and a negative sq is moved into sf as (-sq)^m (-sf))."""
    base, ex = pw.base, pw.exp
    m = ex.q
    num, den = sp.fraction(sp.together(base))
    if m % 2 == 1 and sample and _sign_fix(den, sample) != den:
        num, den = -num, -den                    # odd m: a positive denominator
    _, sfl = sp.sqf_list(sp.expand(num * den ** (m - 1)))
    sq, sf = sp.S(1), sp.S(1)
    for fac, j in sfl:
        sq *= fac ** (j // m)
        sf *= fac ** (j % m)
    const = sp.cancel(sp.expand(num * den ** (m - 1)) / (sq ** m * sf))
    sqf = _sign_fix(sq, sample)
    if sqf != sq and m % 2 == 1:
        const = -const                           # sq^m sf = (-sq)^m (-sf)
    sq = sqf
    # sqrt(N/D) = sqrt(N D)/|D|: the sign of D on the domain enters for odd k
    dsgn = sp.S(-1) if (m % 2 == 0 and sample and _sign_fix(den, sample) != den) else sp.S(1)
    dsgn = dsgn ** ex.p
    # pure-root factors: a factor of the squarefree radicand that is itself a
    # generator g, positive at the sample point, is split off as g^ex so that
    # it flattens (Lemma 3.2): sqrt(2 t (1 + t^2)) = sqrt(2) sqrt(t) sqrt(1 + t^2)
    pure, rest = sp.S(1), const
    for fac, j in sp.factor_list(sf)[1]:
        if (j == 1 and fac in vars_ and isinstance(fac, sp.Symbol) and fac.is_positive
                and _sign_fix(fac, sample) == fac):        # a generator, not the radical symbol y
            pure *= sp.Pow(fac, ex)
        else:
            rest *= fac ** j
    sf = sp.expand(rest)                # expanded: a product form would invite further automatic splitting
    if sf.free_symbols.isdisjoint(set(vars_)):
        return sp.together(dsgn * sq ** (m * ex) * sf ** ex / den ** (m * ex)) * pure
    return sp.together(dsgn * sq ** (m * ex) / den ** (m * ex)) * pure * sp.Pow(sf, ex)


def _sample_point(expr, x):
    """A rational x0 at which every radicand and inverse-function argument of
    the integrand is in its real domain; None if none of the candidates is."""
    rads = [(z.base, z.exp.q) for z in expr.atoms(sp.Pow) if z.exp.is_Rational and not z.exp.is_Integer]
    def okay(x0):
        try:
            for b, mr in rads:
                v = complex(sp.N(b.subs(x, x0)))
                # even roots need a positive radicand; odd roots a nonzero real one
                if abs(v.imag) > 1e-12 or (v.real <= 0 if mr % 2 == 0 else v.real == 0):
                    return False
            for f in expr.atoms(sp.Function):
                a = complex(sp.N(f.args[0].subs(x, x0)))
                if abs(a.imag) > 1e-12:
                    return False
                if isinstance(f, (sp.asin, sp.acos)) and not (-1 < a.real < 1):
                    return False
                if isinstance(f, sp.acosh) and not a.real > 1:
                    return False
                if isinstance(f, sp.atanh) and not (-1 < a.real < 1):
                    return False
                if isinstance(f, (sp.acoth, sp.asec, sp.acsc)) and not abs(a.real) > 1:
                    return False
                if isinstance(f, sp.asech) and not (0 < a.real < 1):
                    return False
                if isinstance(f, sp.acsch) and a.real == 0:
                    return False
                if isinstance(f, sp.log) and not a.real > 0:
                    return False
            v = complex(sp.N(expr.subs(x, x0)))
            return abs(v.imag) < 1e-9 and abs(v) < 1e12
        except (TypeError, ValueError, ZeroDivisionError):
            return False
    for x0 in (sp.Rational(1, 2), 2, sp.Rational(1, 3), 3, sp.Rational(3, 2), sp.Rational(1, 5), 5,
               sp.Rational(-1, 2), -2, sp.Rational(7, 10), sp.Rational(3, 10)):
        if okay(x0):
            return x0
    return None


def build_tower(integrand, x, verbose=False):
    expr = sp.sympify(integrand)
    gens, derivs, q, m = [x], [(sp.S(1), sp.S(0))], None, 2
    Y = sp.Dummy('Y')
    back = []                       # ordered (old, new) substitutions for the result
    T = Tower(gens, derivs, q, m)
    counter = [0]
    x0 = _sample_point(expr, x)
    sample = {x: x0} if x0 is not None else {}     # numeric values of the generators at x0

    def record(sym, surface):
        """value of a new generator at the sample point, from its surface expression"""
        if sample:
            try:
                v = complex(sp.N(surface.subs(sample)))
                sample[sym] = sp.Float(v.real, 30) if abs(v.imag) < 1e-12 else None
            except (TypeError, ValueError):
                sample[sym] = None
            if sample[sym] is None:
                del sample[sym]
        if q is not None and Y not in sample and sample:
            try:
                sample[Y] = sp.N(q.subs(sample)) ** sp.Rational(1, m)
            except (TypeError, ValueError):
                pass

    def new_sym(prefix):
        counter[0] += 1
        return sp.Symbol(f"{prefix}{counter[0]}", positive=True)

    def rebuild_tower():
        nonlocal T
        T = Tower(gens, derivs, q, m)

    def is_cand_arg(a):
        vars_ = gens + [Y]
        aa = _rad_rules(a, q, Y, m)
        return _rational_in(aa, vars_) and not aa.free_symbols.isdisjoint(set(vars_))

    def to_tuple(a):
        """coordinates of an expression in the generators and the radical"""
        return T.from_Y(_rad_rules(a, q, Y, m), Y)

    # --- Euler parametrisation of a conic when a second radical is demanded
    def euler_step():
        nonlocal expr, q, gens, derivs, Y
        from parallel_mixed import _rational_point
        if m != 2:                                 # a conic y^2 = q only
            return False
        for g in gens:
            P = sp.Poly(q, g) if q.is_polynomial(g) else None
            if P is None or P.degree() != 2 or not all(c.free_symbols.isdisjoint(set(gens)) for c in P.all_coeffs()):
                continue
            a2, b2, c2 = P.all_coeffs()
            alpha = sp.sqrt(a2)
            w = new_sym('w')
            if alpha.is_rational:
                # Euler's first substitution through the point at infinity, in
                # the form y = -alpha g + w, i.e. w = y + alpha g: the LARGE root,
                # positive for large positive g, so that the formal
                # normalisations sqrt(P/w^2) = sqrt(P)/w hold on the natural
                # real domain (w = y - alpha g would be negative there and flip
                # the sign of the result)
                gw = sp.cancel((w ** 2 - c2) / (b2 + 2 * alpha * w))
                yw = sp.cancel(w - alpha * gw)
                Dw = T.D((alpha * g, sp.S(1)))
                w_surface = sp.sqrt(q) + alpha * g
            else:
                # through a rational point (g0, y0): y = y0 + w (g - g0)
                pt = _rational_point(q, g)
                if pt is None:
                    continue
                g0, y0 = pt
                gw = sp.cancel((2 * y0 * w - (a2 + w ** 2) * g0 - b2) / (a2 - w ** 2))
                yw = sp.cancel(y0 + w * (gw - g0))
                Dg = derivs[gens.index(g)]
                from parallel_mixed import _padd, _pscale, _pmul
                num = _padd(_pscale(g - g0, T.Dy), _pscale(-1, _pmul((-y0, sp.S(1)), Dg, q)))
                Dw = _pscale(1 / (g - g0) ** 2, num)
                w_surface = (sp.sqrt(q) - y0) / (g - g0)
            # the generator symbols carry a positivity assumption (used by the
            # radical normalisations), so the parameter must be positive on the
            # domain: if w is negative at the sample point, use -w instead
            if sample:
                try:
                    vw = complex(sp.N(w_surface.subs(sample)))
                    if abs(vw.imag) < 1e-12 * max(1.0, abs(vw.real)) and vw.real < 0:
                        gw, yw = gw.subs(w, -w), yw.subs(w, -w)
                        Dw = (sp.cancel(-Dw[0]), sp.cancel(-Dw[1]))
                        w_surface = -w_surface
                except (TypeError, ValueError):
                    pass
            Dw = sp.cancel((Dw[0] + Dw[1] * Y).subs({Y: yw, g: gw}))
            new_derivs = []
            for gg, d in zip(gens, derivs):
                if gg == g:
                    new_derivs.append((Dw, sp.S(0)))
                else:
                    new_derivs.append((sp.cancel((d[0] + d[1] * Y).subs({Y: yw, g: gw})), sp.S(0)))
            # earlier back rules may mention this radical's symbol Y (e.g. a
            # generator log(g + Y)): record what Y was, then retire the symbol
            back.append((Y, sp.sqrt(q)))
            back.append((w, w_surface))
            record(w, w_surface)
            sample.pop(Y, None)
            expr = _rad_rules(expr, q, Y).subs({Y: yw, g: gw})
            gens = [w if gg == g else gg for gg in gens]
            derivs = new_derivs
            q = None
            Y = sp.Dummy('Y')
            rebuild_tower()
            return True
        return False

    # --- trigonometric family through a tangent (parity rules first)
    def trig_step(a, hyper):
        nonlocal expr, q, gens, derivs
        s, c, r = sp.Dummy('s'), sp.Dummy('c'), sp.Dummy('r')
        fam = HYP if hyper else TRIG
        rules = ({sp.sinh(a): s, sp.cosh(a): c, sp.tanh(a): s / c, sp.coth(a): c / s, sp.sech(a): 1 / c, sp.csch(a): 1 / s}
                 if hyper else
                 {sp.sin(a): s, sp.cos(a): c, sp.tan(a): s / c, sp.cot(a): c / s, sp.sec(a): 1 / c, sp.csc(a): 1 / s})
        e1 = expr.subs(rules)
        # sub-expressions that are not rational in (s, c) -- the bases of radicals
        # and the arguments of opaque functions such as log(sin x) -- are replaced
        # by placeholders, innermost first; each must obey the same parity rule as
        # the whole, and is rebuilt after the rule has fired
        items = []                                     # (placeholder, inner expression, rebuild)
        e2 = e1
        def opaque(e):
            return sorted([f for f in e.atoms(sp.Function) if not f.free_symbols.isdisjoint({s, c})],
                          key=sp.count_ops)
        def radbases(e):
            return sorted({z.base for z in e.atoms(sp.Pow) if z.exp.is_Rational and not z.exp.is_Integer
                           and not z.base.free_symbols.isdisjoint({s, c})}, key=sp.count_ops)
        while True:
            fs, bs_ = opaque(e2), radbases(e2)
            if not fs and not bs_:
                break
            if fs:
                f0 = fs[0]
                p_ = sp.Dummy('o')
                items.append((p_, f0.args[0], f0.func))
                e2 = e2.xreplace({f0: p_})
            else:
                b0 = bs_[0]
                p_ = sp.Dummy('b')
                items.append((p_, b0, lambda z: z))
                e2 = e2.xreplace({b0: p_})
        def reduce_all(sub_var, rv, qq):
            """(reduced inner expressions, reduced outer) as pairs, or None if not rational"""
            try:
                inner = [_pair_reduce(b.subs(sub_var, rv), rv, qq) for _, b, _ in items]
                outer = _pair_reduce(e2.subs(sub_var, rv), rv, qq)
            except (sp.PolynomialError, sp.polys.polyerrors.PolynomialError, TypeError):
                return None
            return inner, outer
        def rebuild(e, parts, sub):
            """substitute the placeholders (any order; a placeholder may occur inside another item)"""
            rep = {p_: fn(b_.subs(sub)) for (p_, _, fn), b_ in zip(items, parts)}
            for _ in range(len(items) + 1):
                e_new = e.xreplace(rep)
                if e_new == e:
                    break
                e = e_new
            return e
        can_change = gens == [x] and a == x and not e1.has(x) and q is None
        if can_change:
            # odd in s: e2 = A(c) + B(c) s with s^2 = 1 - c^2 (cosh: c^2 - 1)
            qs = 1 - c ** 2 if not hyper else c ** 2 - 1
            got = reduce_all(s, r, qs)
            if got is not None:
                bs, outer = got
                if all(b_[1] == 0 for b_ in bs) and outer[0] == 0:
                    u = new_sym('u')
                    expr = rebuild(((1 if hyper else -1) * outer[1]).subs(c, u), [b_[0] for b_ in bs], {c: u})
                    gens, derivs = [u], [(sp.S(1), sp.S(0))]
                    back.append((u, sp.cosh(a) if hyper else sp.cos(a)))
                    record(u, sp.cosh(a) if hyper else sp.cos(a))
                    rebuild_tower()
                    return
            # odd in c: e2 = A(s) + B(s) c with c^2 = 1 - s^2 (cosh: 1 + s^2)
            qc = 1 - s ** 2 if not hyper else 1 + s ** 2
            got = reduce_all(c, r, qc)
            if got is not None:
                bc, outer = got
                if all(b_[1] == 0 for b_ in bc) and outer[0] == 0:
                    u = new_sym('u')
                    expr = rebuild(outer[1].subs(s, u), [b_[0] for b_ in bc], {s: u})
                    gens, derivs = [u], [(sp.S(1), sp.S(0))]
                    back.append((u, sp.sinh(a) if hyper else sp.sin(a)))
                    record(u, sp.sinh(a) if hyper else sp.sin(a))
                    rebuild_tower()
                    return
        # even in (s, c): t = tan a, s -> t r, c -> r with r^2 = 1/(1 + t^2) (tanh: 1/(1 - t^2))
        tn = new_sym('t')
        qr = 1 / (1 - tn ** 2) if hyper else 1 / (1 + tn ** 2)
        Da = T.D(to_tuple(a))
        try:
            bs = [_pair_reduce(b.subs({s: tn * r, c: r}), r, qr) for _, b, _ in items]
            outer = _pair_reduce(e2.subs({s: tn * r, c: r}), r, qr)
            even = all(b_[1] == 0 for b_ in bs) and outer[1] == 0
        except (sp.PolynomialError, sp.polys.polyerrors.PolynomialError, TypeError):
            even = False
        if even:
            expr = rebuild(outer[0], [b_[0] for b_ in bs], {})
            Dt = tuple(_c(((1 - tn ** 2) if hyper else (1 + tn ** 2)) * d) for d in Da)
            back.append((tn, sp.tanh(a) if hyper else sp.tan(a)))
            record(tn, sp.tanh(a) if hyper else sp.tan(a))
        else:
            half = ({s: 2 * tn / (1 - tn ** 2), c: (1 + tn ** 2) / (1 - tn ** 2)} if hyper
                    else {s: 2 * tn / (1 + tn ** 2), c: (1 - tn ** 2) / (1 + tn ** 2)})
            expr = e1.subs(half)
            Dt = tuple(_c(((1 - tn ** 2) / 2 if hyper else (1 + tn ** 2) / 2) * d) for d in Da)
            back.append((tn, sp.tanh(a / 2) if hyper else sp.tan(a / 2)))
            record(tn, sp.tanh(a / 2) if hyper else sp.tan(a / 2))
        gens.append(tn); derivs.append(Dt)
        rebuild_tower()

    # general powers a^b with a non-rational exponent are exp(b log a)
    expr = expr.replace(lambda z: isinstance(z, sp.Pow) and not z.exp.is_Rational
                        and not z.exp.free_symbols.isdisjoint({x}) and z.base != sp.E,
                        lambda z: sp.exp(z.exp * sp.log(z.base)))

    # --- main loop
    while True:
        # trigonometric families first
        trig = [f for f in expr.atoms(sp.Function) if isinstance(f, TRIG + HYP) and is_cand_arg(f.args[0])]
        if trig:
            f0 = min(trig, key=sp.count_ops)
            trig_step(f0.args[0], isinstance(f0, HYP))
            continue
        cands = [f for f in expr.atoms(sp.Function) if isinstance(f, GEN_HEADS) and is_cand_arg(f.args[0])]
        cands += [z for z in expr.atoms(sp.Pow) if z.exp.is_Rational and not z.exp.is_Integer
                  and is_cand_arg(z.base)]
        if not cands:
            break
        cnd = min(cands, key=sp.count_ops)
        if isinstance(cnd, sp.Pow):
            nrm = _root_normalize(cnd, gens + [Y], sample)
            if nrm != cnd:
                expr = expr.xreplace({cnd: nrm})
                continue
            base, r_ = cnd.base, cnd.exp
            mm = r_.q                                   # the degree of this root
            # flattenable root (Lemma 3.2)
            g_fl = None
            for g in gens:
                # c g + r with c a constant and r free of g; neither may involve y
                # (a coefficient in y is not a pure root of the generator)
                if base.is_polynomial(g) and sp.Poly(base, g).degree() == 1 and not base.has(Y) and \
                        sp.Poly(base, g).all_coeffs()[0].free_symbols.isdisjoint(set(gens)):
                    g_fl = g
                    break
            if g_fl is not None:
                g = g_fl
                coef = sp.Poly(base, g).all_coeffs()[0]
                rest = base.subs(g, 0)
                u = new_sym('u')
                Dbase = T.D(to_tuple(base))
                pos = gens.index(g)
                Du = tuple(_c(d / (mm * u ** (mm - 1))) for d in Dbase)
                sub = {g: (u ** mm - rest) / coef}
                derivs = [tuple(_c(dd.subs(sub)) for dd in (Du if i == pos else derivs[i])) for i in range(len(gens))]
                gens = [u if gg == g else gg for gg in gens]
                if q is not None:
                    q = sp.expand(q.subs(sub))
                back.append((u, base ** sp.Rational(1, mm)))
                record(u, (base.subs(Y, q ** sp.Rational(1, m)) if q is not None else base) ** sp.Rational(1, mm))
                expr = expr.replace(lambda z: isinstance(z, sp.Pow) and z.exp.is_Rational and sp.expand(z.base - base) == 0,
                                    lambda z: u ** (mm * z.exp))
                expr = expr.subs(sub)
                rebuild_tower()
                continue
            # the simple radical y^m = base
            if q is not None and sp.expand(base - q) != 0:
                if euler_step():
                    continue
                raise TowerError(f"two unflattenable radicals: {q} and {base}")
            if q is not None:
                # the radicand of the tower under another root base^(k/mm), mm | m
                if m % mm != 0:
                    raise TowerError(f"roots of degree {m} and {mm} of the same radicand {q}")
                expr = _rad_rules(expr, q, Y, m)
                continue
            if not base.is_polynomial(*gens):
                raise TowerError(f"radicand {base} is not a polynomial in the generators")
            # every root of this radicand in the integrand: m = lcm of their degrees
            degs = {z.exp.q for z in expr.atoms(sp.Pow) if z.exp.is_Rational and not z.exp.is_Integer
                    and sp.expand(z.base - base) == 0}
            m = int(sp.ilcm(*degs)) if len(degs) > 1 else mm
            if any(j >= m for _, j in sp.sqf_list(sp.expand(base), *gens)[1]):
                raise TowerError(f"radicand {base} is not {m}-th-power-free")
            q = base
            if m > 2:
                derivs = [tuple(d) + (sp.S(0),) * (m - 2) for d in derivs]
            expr = _rad_rules(expr, q, Y, m)
            rebuild_tower()
            if sample:
                try:
                    sample[Y] = sp.N(q.subs(sample)) ** sp.Rational(1, m)
                except (TypeError, ValueError):
                    pass
            continue
        # transcendental generator
        f0 = cnd
        a = f0.args[0]
        ap = to_tuple(a)
        Da = T.D(ap)
        tn = new_sym('t')
        head = type(f0)
        rcoef = sp.S(1)                        # 1/sqrt(rad) = (1/rcoef) * y/q after normalisation
        icoef = sp.S(1)                        # coefficient of D a in D t, from the table
        if head in INV_RADICAL:
            rad_f, coef_f, absQ = INV_RADICAL[head]
            rad = sp.together(rad_f(a))
            icoef = coef_f(a)
            if absQ and sample:               # the derivative carries |a|
                try:
                    av = complex(sp.N(a.subs(Y, sp.sqrt(q) if q is not None else Y).subs(sample)))
                    if av.real < 0:
                        icoef = -icoef
                except (TypeError, ValueError):
                    pass
            rad = _rad_rules(rad, q, Y, m)
            # normalise sqrt(rad) = rcoef * sqrt(sf) with sf a squarefree polynomial
            # (done on rad itself: SymPy would auto-split sqrt of a quotient)
            num_, den_ = sp.fraction(sp.together(rad))
            _, sfl_ = sp.sqf_list(sp.expand(num_ * den_))
            sq_, sf = sp.S(1), sp.S(1)
            for fac_, j_ in sfl_:
                sq_ *= fac_ ** (j_ // 2)
                sf *= fac_ ** (j_ % 2)
            sf = sp.expand(sf * sp.cancel(sp.expand(num_ * den_) / (sq_ ** 2 * sf)))
            sq_ = _sign_fix(sq_, sample)
            dsgn_ = sp.S(-1) if (sample and _sign_fix(den_, sample) != den_) else sp.S(1)
            if not sf.free_symbols.isdisjoint(set(gens + [Y])):
                rcoef = sp.cancel(dsgn_ * sq_ / den_)          # sqrt(N/D) = sqrt(N D)/|D|
                if q is None:
                    q, m = sp.expand(sf), 2
                    rebuild_tower()
                    Da = T.D(ap)
                    expr = _rad_rules(expr, q, Y, m)
                elif sp.expand(sf - q) != 0:
                    if euler_step():
                        continue
                    raise TowerError(f"the derivative of {f0} needs the radical sqrt({sf}) but the tower has y^{m} = {q}")
                elif m != 2:
                    raise TowerError(f"the derivative of {f0} needs sqrt({sf}) but the tower has the radical y^{m} = {q}")
            else:
                rcoef = sp.cancel(dsgn_ * sq_ * sp.sqrt(sf) / den_)   # no radical at all: D t is rational
                head = None
        if head is sp.log:
            Dt = T.div(Da, ap)
        elif head in INV_RATIONAL:
            Dt = T.mul(Da, to_tuple(INV_RATIONAL[head](a)))
        elif head in INV_RADICAL:
            cp = to_tuple(icoef / rcoef)
            Dt = T.mul(T.mul(Da, cp), (sp.S(0), 1 / q))       # 1/sqrt(q) = y/q (m = 2)
        elif head is None:                    # inverse function whose radical disappeared
            Dt = T.mul(Da, to_tuple(icoef / rcoef))
        elif head is sp.exp:
            Dt = tuple(_c(tn * d) for d in Da)
        elif head is sp.tan:
            Dt = tuple(_c((1 + tn ** 2) * d) for d in Da)
        elif head is sp.cot:
            Dt = tuple(_c(-(1 + tn ** 2) * d) for d in Da)
        elif head in (sp.tanh, sp.coth):
            Dt = tuple(_c((1 - tn ** 2) * d) for d in Da)
        else:
            raise TowerError(f"unsupported generator {f0}")
        gens.append(tn); derivs.append(Dt)
        back.append((tn, f0))
        record(tn, f0.subs(Y, q ** sp.Rational(1, m)) if q is not None else f0)
        expr = expr.xreplace({f0: tn})
        rebuild_tower()

    expr = _rad_rules(expr, q, Y, m)
    if not _rational_in(expr, gens + [Y]) or (q is None and expr.has(Y)):
        raise TowerError(f"could not reduce the integrand to a rational function of the generators and y: {expr}")
    fpair = T.from_Y(expr, Y)
    if q is not None:
        back.append((Y, q ** sp.Rational(1, m)))
    if verbose:
        print(f"  tower: generators {gens} with D = {derivs}" + (f", y^{m} = {q}" if q is not None else ""))
        print(f"  integrand: {fpair}")
    return T, fpair, back


def _substitute_back(res, back):
    """apply the back rules until nothing changes (they may introduce earlier symbols)"""
    for _ in range(len(back) + 2):
        new = res
        for old, val in reversed(back):
            new = new.subs(old, val)
        if new == res:
            break
        res = new
    return res


def integrate_surface(integrand, x, verbose=False, verify=False, **opts):
    """The surface-form entry point: integrate an expression in x."""
    T, fpair, back = build_tower(integrand, x, verbose=verbose)
    res = parallel_integrate_mixed(fpair, T, verbose=verbose, **opts)
    if not isinstance(res, sp.Basic):
        return tuple(_substitute_back(r, back) if isinstance(r, sp.Basic) else r for r in res)
    surf = _substitute_back(res, back)
    if verify:
        ok = all(abs(complex(sp.N((sp.diff(surf, x) - integrand).subs(x, p), 30))) < 1e-20
                 for p in (sp.Rational(1, 3), sp.Rational(1, 2), 2))
        if not ok:
            print("  WARNING: numeric verification of D(result) - integrand failed")
    return surf
