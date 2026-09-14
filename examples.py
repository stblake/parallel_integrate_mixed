"""examples.py -- runs every example and benchmark of

    Parallel Integration over Simple Radical Extensions II: Mixed Towers

through the merged pipeline parallel_mixed.py, in the order of Section 10,
followed by the two certificate sessions of Remark 9.1 / Proposition 9.2 and a
few regressions not printed in the paper.  Each case records the
outcome the paper claims (an elementary integral, a non-elementarity
certificate, or an honest 'failed'); every returned integral is checked once
more here by differentiating the surface expression where one is supplied.

    python examples.py            # everything (~7 minutes; Günther dominates)
    QUICK=1 python examples.py    # skip the two slowest benchmarks
"""
import os, sys, time
import sympy as sp
from parallel_mixed import Tower, parallel_integrate_mixed as PIM

x, t, u = sp.symbols('x t u', positive=True)
S = sp.S
q = x**2 + 1
QUICK = os.environ.get('QUICK') == '1'
results = []


def check_integral(I, surface_f, subs, var):
    """verify D(I) = f on the surface, after substituting the tower generators."""
    Is = I.subs(subs)
    for pt in (sp.Rational(3, 2), 2, sp.Rational(7, 3)):
        v = sp.N((sp.diff(Is, var) - surface_f).subs(var, pt), 30)
        if abs(complex(v)) > 1e-20:
            return False
    return True


def run(label, f, T, expect, surface=None, subs=None, var=x, verbose=False, slow=False):
    """expect: 'integral' | 'not elementary' | 'failed'"""
    if slow and QUICK:
        print(f"[{label}] skipped (QUICK)"); return
    print(f"\n### {label}")
    t0 = time.time()
    r = PIM(f, T, verbose=verbose)
    dt = time.time() - t0
    if expect == 'integral':
        ok = isinstance(r, sp.Basic)
        if ok and surface is not None:
            ok = check_integral(r, surface, subs or {}, var)
        print(str(r)[:300] + (' ...' if len(str(r)) > 300 else ''))
    else:
        ok = isinstance(r, tuple) and str(r[0]).startswith(expect)
        print(r)
    results.append((label, expect, ok, dt))
    print(f"--> {'PASS' if ok else 'FAIL'}  ({dt:.1f}s)")


# ================================================================ Section 10
ys = sp.sqrt(q)                                   # y over the flagship curve
tl = sp.log(x + ys)                               # t = log(x + y)

run("10.1 flagship: int log(x+sqrt(x^2+1))", (t, 0),
    Tower([x, t], [(1, 0), (0, 1/q)], q=q),
    'integral', surface=tl, subs={t: tl})

run("10.2 irreplaceable unit (t = exp y)", (0, (1 + x*t)/q),
    Tower([x, t], [(1, 0), (0, x*t/q)], q=q),
    'integral', surface=(1 + x*sp.exp(ys))/ys, subs={t: sp.exp(ys)})

run("10.3 moving prime: not elementary", (1/(x*t), 0),
    Tower([x, t], [(1, 0), (0, 1/q)], q=q), 'not elementary', verbose=True)

run("10.4 Bronstein (E): not elementary", (t**2/(1 + t**2), 1/(1 + t**2)),
    Tower([x, t], [(1, 0), (1/(2*x*t), 0)], q=t**2 + t), 'not elementary', verbose=True)

run("10.5 exp(sqrt x) (flattened)", (t, 0),
    Tower([u, t], [(1/(2*u), 0), (t/(2*u), 0)]), 'integral',
    surface=sp.exp(sp.sqrt(x)), subs={u: sp.sqrt(x), t: sp.exp(sp.sqrt(x))})

run("10.6 tan(sqrt x)/sqrt x (flattened)", (t/u, 0),
    Tower([u, t], [(1/(2*u), 0), ((1 + t**2)/(2*u), 0)]), 'integral',
    surface=sp.tan(sp.sqrt(x))/sp.sqrt(x), subs={u: sp.sqrt(x), t: sp.tan(sp.sqrt(x))}, verbose=True)

run("10.7 tan over the curve (elementary instance)", (x*(1 + t**2), 3*x*t/q),
    Tower([x, t], [(1, 0), (0, x*(1 + t**2)/q)], q=q), 'integral',
    surface=x*(1 + sp.tan(ys)**2) + 3*x*sp.tan(ys)/ys, subs={t: sp.tan(ys)})
# 10.7, non-elementary instance: certified by the residue -y/x at v_oo
run("10.7 int tan(sqrt(x^2+1)) dx: not elementary (residue at v_oo)", (t, 0),
    Tower([x, t], [(1, 0), (0, x*(1 + t**2)/q)], q=q), 'not elementary', verbose=True)

run("10.8 curve-split moving logands",
    (-(1 + 5*x)/(t**2 - x**2 - 1), (t**3 + (4 + x - x**2)*t)/(q*(t**2 - x**2 - 1))),
    Tower([x, t], [(1, 0), (0, 1/q)], q=q), 'integral',
    surface=(tl**3 + (4 + x - x**2)*tl - (1 + 5*x)*ys)/(ys*(tl**2 - x**2 - 1)),
    subs={t: tl}, verbose=True)

u14 = sp.sqrt(x + sp.log(x))
run("10.9 tutorial Ex 14 (flattened)", ((x + 1)/(x*u) + (2*x*u + x + 1)/(x*u*(x + u)), 0),
    Tower([x, u], [(1, 0), ((x + 1)/(2*x*u), 0)]), 'integral',
    surface=((x**2 + 2*x + 1)*u14 + (3*x + 1)*sp.log(x) + 3*x**2 + x)/((x*sp.log(x) + x**2)*u14 + x**2*sp.log(x) + x**3),
    subs={u: u14})

u15 = (x + sp.exp(x))**sp.Rational(1, 3)
run("10.10 tutorial Ex 15 (flattened)", (((2*x**2 + 3*x)*u**3 + 3*u + 2*x**2 - 2*x**3)/(x*u), 0),
    Tower([x, u], [(1, 0), ((u**3 - x + 1)/(3*u**2), 0)]), 'integral',
    surface=(3*u15 + (2*x**2 + 3*x)*sp.exp(x) + 5*x**2)/(x*u15), subs={u: u15})


# 10.11 Bronstein 1990, pp. 134 and 147 (same flattenable curve as Ex 14)
Tj = Tower([x, u], [(1, 0), ((x + 1)/(2*x*u), 0)])
run("10.11 JSC90 p.134: (x+1)/((x log x + x^2) sqrt(x+log x))", ((x + 1)/(x*u**3), 0), Tj,
    'integral', surface=(x + 1)/((x*sp.log(x) + x**2)*u14), subs={u: u14}, verbose=True)
run("10.11 JSC90 p.147 as printed (x^2+x+1): not elementary",
    (sp.cancel(((x**2 + x + 1)*u + (3*x + 1)*(u**2 - x) + 3*x**2 + x)
               / ((x*(u**2 - x) + x**2)*u + x**2*(u**2 - x) + x**3)), 0), Tj,
    'not elementary', verbose=True)
run("10.11 JSC90 p.147 corrected, lowest terms: ((x+1)^2 + (3x+1)u)/(x u (u+x))",
    (sp.cancel(((x + 1)**2 + (3*x + 1)*u)/(x*u*(u + x))), 0), Tj, 'integral',
    surface=((x + 1)**2 + (3*x + 1)*u14)/(x*u14*(u14 + x)), subs={u: u14}, verbose=True)

q71 = x**4 + 10*x**2 - 96*x - 71
run("10.12 Cohen 1993", (0, x/q71), Tower([x], [(S(1), S(0))], q=q71),
    'integral', surface=x/sp.sqrt(q71), verbose=True)

q6 = x**6 + 4*x**5 + 6*x**4 - 12*x**3 + 33*x**2 - 16*x
run("10.13 Schultz 2015 (genus 2)", (0, (29*x**2 + 18*x - 3)/q6),
    Tower([x], [(S(1), S(0))], q=q6), 'integral',
    surface=(29*x**2 + 18*x - 3)/sp.sqrt(q6), verbose=True)

q3 = x**3 + 1
y3 = sp.sqrt(q3)
run("10.14 Bronstein ISSAC'91", ((5*x**4 + 2*x - 2)*t/x**2, (5*x**4 + x**3 + 2*x - 2)*t/(x**2*q3)),
    Tower([x, t], [(1, 0), (0, t*(5*x**3 + 2)/(2*q3))], q=q3), 'integral',
    surface=(((5*x**4 + 2*x - 2)/x**2)*(1 + 1/y3) + x/y3)*sp.exp(x*y3),
    subs={t: sp.exp(x*y3)}, verbose=True)

q4 = x**4 + 4*x**3 + 2*x**2 + 1
N4 = 2*x**6 + 4*x**5 + 7*x**4 - 3*x**3 - x**2 - 8*x - 8
run("10.15 Chebyshev (Davenport Ex. 5)", (0, N4/((2*x**2 - 1)**2*q4)),
    Tower([x], [(S(1), S(0))], q=q4), 'integral',
    surface=N4/((2*x**2 - 1)**2*sp.sqrt(q4)), verbose=True, slow=True)

run("10.16 Günther 1882 (order-6 torsion)", (0, x/((x**3 + 8)*(x**3 - 1))),
    Tower([x], [(S(1), S(0))], q=x**3 - 1), 'integral',
    surface=x/((x**3 + 8)*sp.sqrt(x**3 - 1)), verbose=True, slow=True)

# ============================================== certificates (Remark 9.1, Prop. 9.2)
run("9.2(b) certified: dx/((x-2) sqrt(x^3+1)) (holomorphic remainder)", (0, 1/((x - 2)*q3)),
    Tower([x], [(S(1), S(0))], q=q3), 'not elementary', verbose=True)

run("10.12 Cohen's -72 variant: not elementary (non-torsion mod p + exact bounds)",
    (0, x/(x**4 + 10*x**2 - 96*x - 72)),
    Tower([x], [(S(1), S(0))], q=x**4 + 10*x**2 - 96*x - 72), 'not elementary', verbose=True)

# ============================================== regressions not printed in the paper
qt = t**2 + 1
yt = sp.sqrt(sp.log(x)**2 + 1)
run("regression (not in paper): torus over the logarithmic tower", (S(5)/(2*x*t), (4*t**3 + 3*t + 1)/(2*x*t*qt)),
    Tower([x, t], [(1, 0), (1/x, 0)], q=qt), 'integral',
    surface=(4*sp.log(x)**3 + 3*sp.log(x) + 1 + 5*yt)/(2*x*sp.log(x)*yt),
    subs={t: sp.log(x)}, verbose=True)


# ============================================ surface forms (build_tower.py)
from build_tower import integrate_surface

def runS(label, f, expect='integral'):
    print(f"\n### {label}")
    t0 = time.time()
    try:
        r = integrate_surface(f, x)
    except Exception as e:
        r = ("error", str(e))
    dt = time.time() - t0
    if expect == 'integral':
        ok = isinstance(r, sp.Basic) and all(
            abs(complex(sp.N((sp.diff(r, x) - f).subs(x, p), 25))) < 1e-15 for p in (sp.Rational(1, 3), sp.Rational(1, 2)))
        print(str(r)[:300] + (' ...' if len(str(r)) > 300 else ''))
    else:
        ok = isinstance(r, tuple) and str(r[0]).startswith(expect)
        print(r)
    results.append((label, expect, ok, dt))
    print(f"--> {'PASS' if ok else 'FAIL'}  ({dt:.1f}s)")

runS("S1  log(x + sqrt(x^2+1))", sp.log(x + sp.sqrt(x**2 + 1)))
runS("S2  exp(sqrt x)", sp.exp(sp.sqrt(x)))
runS("S3  tan(sqrt x)/sqrt x", sp.tan(sp.sqrt(x))/sp.sqrt(x))
runS("S4  arctan(x)/sqrt x  (ArcTan primitive, split specials)", sp.atan(x)/sp.sqrt(x))
runS("S5  arctan(sqrt x)", sp.atan(sp.sqrt(x)))
runS("S6  arcsin(x)  (radical introduced by the derivative)", sp.asin(x))
runS("S7  log(x) arcsin(x)  (S'-unit over the special x)", sp.log(x)*sp.asin(x))
runS("S8  arcsin(sqrt(x+1) - sqrt x)  (Euler parametrisation of the conic)", sp.asin(sp.sqrt(x + 1) - sp.sqrt(x)))
runS("S9  cos^2 x / sqrt(cos^4 x + cos^2 x + 1)  (t = tan x, cubic model, Miller S'-units)",
     sp.cos(x)**2/sp.sqrt(sp.cos(x)**4 + sp.cos(x)**2 + 1))
runS("S10 tan(x)/sqrt(1 + sec^3 x)  (odd in sin: u = cos x)", sp.tan(x)/sp.sqrt(1 + sp.sec(x)**3))
runS("S11 tan(x) sqrt(1 + tan^4 x)  (radical over the tangent)", sp.tan(x)*sp.sqrt(1 + sp.tan(x)**4))
runS("S12 sqrt(tan x)  (specials split over Fbar)", sp.sqrt(sp.tan(x)))
runS("S13 sqrt(log x): not elementary, honest 'failed'", sp.sqrt(sp.log(x)), 'failed')
runS("S14 exp(x^2): not elementary, honest 'failed'", sp.exp(x**2), 'failed')
runS("S15 Bronstein (E) nested radical: not elementary",
     (sp.log(x) + sp.sqrt(sp.log(x) + sp.sqrt(sp.log(x))))/(1 + sp.log(x)), 'not elementary')
runS("S16 sqrt(sin x)/(1 + sin^2 x)  (Charlwood A27: residues at the degree-8 prime in the residue field)",
     sp.sqrt(sp.sin(x))/(1 + sp.sin(x)**2))

# ================================================================ m >= 3
# radicals of degree m >= 3 (elements on the Trager basis w_i = y^i/E_i):
# unit logands from the divisor search at the places at infinity, residue
# classes in the residue field with the m x m norm, realisation by Hensel
# lifting and linear algebra with the pole orders at infinity distributed
runS("M1  1/(x^3-1)^(1/3)  (Fermat cubic: units at the three places at infinity)",
     1/(x**3 - 1)**sp.Rational(1, 3))
runS("M2  1/(x (x^3+1)^(1/3))  (residue classes over x, 3-torsion, logands y - zeta)",
     1/(x*(x**3 + 1)**sp.Rational(1, 3)))
runS("M3  1/(x (x^2-1)^(1/3))  (one place at infinity, 2-torsion classes)",
     1/(x*(x**2 - 1)**sp.Rational(1, 3)))
runS("M4  x^2 log(x)/(x^3+1)^(2/3) + (x^3+1)^(1/3)/x  (log above the cube root)",
     x**2*sp.log(x)/(x**3 + 1)**sp.Rational(2, 3) + (x**3 + 1)**sp.Rational(1, 3)/x)
runS("M5  1/(x (x^4+1)^(1/4))  (m = 4, residue classes over Q(i))",
     1/(x*(x**4 + 1)**sp.Rational(1, 4)))
runS("M6  1/(x^4+1)^(1/4)  (m = 4, units at the four places at infinity)",
     1/(x**4 + 1)**sp.Rational(1, 4))
runS("M7  x/(x^3-1)^(1/3): not elementary, honest 'failed'", x/(x**3 - 1)**sp.Rational(1, 3), 'failed')

# ================================================================ summary
print("\n" + "=" * 78)
w = max(len(r[0]) for r in results)
for label, expect, ok, dt in results:
    print(f"{label:<{w}}  {expect:<15} {'PASS' if ok else 'FAIL'}  {dt:6.1f}s")
print("=" * 78)
nfail = sum(1 for r in results if not r[2])
print(f"{len(results) - nfail}/{len(results)} passed")
sys.exit(1 if nfail else 0)
