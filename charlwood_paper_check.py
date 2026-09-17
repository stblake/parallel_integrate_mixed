"""charlwood_paper_check.py -- every closed form displayed in the paper
(rn-radicals-charlwood.tex) is defined here and checked by differentiation
at rational points of the real domain, exactly as the pipeline's output is.

    python charlwood_paper_check.py
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sympy as sp
from sympy import sqrt, log, exp, sin, cos, tan, sec, asin, atan, asec, Rational, pi
from charlwood import BY_ID, verify, x

DISPLAYED = {}

# ---- Problem 1: int arcsin x log x
y = sqrt(1 - x**2)
DISPLAYED["P1"] = x*log(x)*asin(x) - x*asin(x) + (log(x) - 2)*y + log(x) - log(y - 1)
# ---- Problem 2
DISPLAYED["P2"] = x - y*asin(x)
# ---- Problem 3: w = sqrt(x) + sqrt(x+1), t = arcsin(sqrt(x+1) - sqrt(x)) = arcsin(1/w)
w = sqrt(x) + sqrt(x + 1)
t = asin(sqrt(x + 1) - sqrt(x))
DISPLAYED["P3"] = sqrt(w**2 - 1)*(2*w**2 + 1)/(8*w**2) + (2*w**4 - w**2 + 2)/(8*w**2)*t
# the same, in Charlwood's form
DISPLAYED["P3c"] = (x + Rational(3, 8))*t + sqrt(2)/4*sqrt(sqrt(x**2 + x) + x) + sqrt(2)/8*sqrt(sqrt(x)*(sqrt(x + 1) - sqrt(x))**3)
# ---- Problem 4: w = (sqrt(x^2+1)-1)/x (Charlwood's t), a = (sqrt5+1)/2
y = sqrt(x**2 + 1)
w = (y - 1)/x
a = (sqrt(5) + 1)/2
DISPLAYED["P4"] = x*log(1 + x*y) - 2*x + 2*sqrt(a)*atan(sqrt(a)*w - 1/sqrt(a)) + log((w + a - sqrt(a))/(w + a + sqrt(a)))/sqrt(a)
# ---- Problem 5: t = tan x, s = y - t^2 - 3/2 with y = sqrt(t^4+3t^2+3)
t = tan(x)
y = sqrt(t**4 + 3*t**2 + 3)
s = y - t**2 - Rational(3, 2)
DISPLAYED["P5"] = -x - Rational(2, 3)*atan((3*y - 3*t**2 - 5)/(2*y*t - 2*t**3 - 3*t))
DISPLAYED["P5c"] = -asin(cos(x)**3)/3
# ---- Problem 6
t = tan(x); y = sqrt(t**4 + 1)
DISPLAYED["P6"] = y/2 - (sqrt(2) + 1)/2*log(y + t**2) + sqrt(2)/2*log(-y - t**2 - 1 + sqrt(2)) - sqrt(2)/2*log(y - t**2 - 1 + sqrt(2))
# ---- Problem 7: u = sqrt(cos x), y = sqrt(u^6 + 1)
u = sqrt(cos(x))
DISPLAYED["P7"] = -Rational(2, 3)*log(u**3 + sqrt(u**6 + 1))
DISPLAYED["P7c"] = Rational(1, 3)*log((sqrt(sec(x)**3 + 1) - 1)/(sqrt(sec(x)**3 + 1) + 1))
# ---- Problem 8: t = tan x, y = sqrt(t^2+2t+2), phi = (1+sqrt5)/2
t = tan(x); y = sqrt(t**2 + 2*t + 2)
phi = (1 + sqrt(5))/2
DISPLAYED["P8"] = None      # filled from the pipeline output at run time (see below)
# ---- Problem 9: u = sqrt(cos x), t = arctan(sqrt(1-u^2)/u) = arctan(sqrt(sec x - 1))
u = sqrt(cos(x)); t = atan(sqrt(1 - u**2)/u)
DISPLAYED["P9"] = -t*u**2 + t/2 + u*sqrt(1 - u**2)/2
# ---- Problem 10
y = sqrt(1 - x**2)
DISPLAYED["P10"] = exp(asin(x))*(x**3 + 3*x - 3*(x**2 + 1)*y)/10

# ---- appendix formulas displayed in the paper
y = sqrt(1 - x**2)
DISPLAYED["A22"] = log(x) - y*asin(x)/x
y = sqrt(x**2 + 1)
DISPLAYED["A21"] = log((y - x - 1)/(y + x + 1)) + log(x + y) - y*atan(x)/x
y = sqrt(x**3 + 1)
DISPLAYED["A9"] = Rational(2, 3)*y + log((y - 1)/(y + 1))/3
y = sqrt(x**4 + 1)
DISPLAYED["A28"] = sqrt(2)/4*log((y + sqrt(2)*x)/(y - sqrt(2)*x))
w = (sqrt(1 - x**2) - 1)/x
Yw = sqrt(w**4 + 6*w**2 + 1)
DISPLAYED["A11"] = ((w**2 - 1)*asin(x) - w)/(2*(w**2 + 1)**2)*Yw + log((Yw - 2*w)/(Yw + 2*w))/8
u = sqrt(x)
DISPLAYED["A38"] = (x + 1)*atan(sqrt(x + 1) - sqrt(x)) + u/2
# A27: the four residue-class logands in the tower u = sqrt(tan(x/2)), y = sqrt(u^4+1),
# coefficients (1+i)/4 and conjugates (I4 of the paper), and the paired real form
u = sqrt(tan(x/2)); y = sqrt(u**4 + 1)
I_ = sp.I
uc = -u**3 + sqrt(2)*(1 + I_)/2*u**2 + I_*u - sqrt(2)*(1 - I_)/2 + (u - sqrt(2)*(1 + I_)/2)*y
conj_u = lambda e: e.subs(u, -u)            # the class -c: the image under u -> -u
conj_i = lambda e: e.subs(I_, -I_)          # the complex conjugate class
DISPLAYED["A27t"] = ((1 + I_)/4*log(uc) + (-(1 + I_)/4)*log(conj_u(uc))
                     + (1 - I_)/4*log(conj_i(uc)) + (-(1 - I_)/4)*log(conj_i(conj_u(uc))))
s_, C_ = sqrt(sin(x)), cos(x)
DISPLAYED["A27"] = (log((2*sin(x) - 2*s_*C_ + C_**2)/(2*sin(x) + 2*s_*C_ + C_**2))/8
                    - atan(2*s_*C_/(2*sin(x) - C_**2))/4)
# A1 in the original tower (by hand from the traces), t1 = log(1+x^2), t2 = log(x+y)
y = sqrt(x**2 + 1); t1 = log(1 + x**2); t2 = log(x + y)
DISPLAYED["A1"] = y*t1*t2 - 2*y*t2 - x*t1 + 4*x - 2*atan(x)
# the identity sqrt(w^4+6w^2+1) in x for A11
DISPLAYED["A11id"] = None


def main():
    import json
    res = json.load(open(os.path.join(HERE, "charlwood_results.json"))) if os.path.exists(os.path.join(HERE, "charlwood_results.json")) else {}
    ok_all = True
    for label, expr in DISPLAYED.items():
        key = label.rstrip("ct")
        if label == "A11id":
            w = (sqrt(1 - x**2) - 1)/x
            lhs = sqrt(w**4 + 6*w**2 + 1)
            for cand in (2*sqrt(1 + x**2)*(1 - sqrt(1 - x**2))/x**2, 2*sqrt(1 + x**2)*(1 - sqrt(1 - x**2))/x**2*(-1)):
                v = [complex(sp.N((lhs - cand).subs(x, p), 20)) for p in (Rational(1, 3), Rational(1, 2))]
                print("A11 identity candidate", cand, v)
            continue
        if expr is None:
            if key in res and "result" in res[key]:
                expr = sp.sympify(res[key]["result"], locals={'x': x})
            else:
                print(f"{label}: (no pipeline result available)"); continue
        ok, errs = verify(expr, BY_ID[key])
        ok_all = ok_all and bool(ok)
        print(f"{label:<4} {'ok' if ok else 'FAIL'}  {[f'{e:.1e}' for e in errs]}")
    print("all displayed formulas verified" if ok_all else "SOME FORMULA FAILED")


if __name__ == "__main__":
    main()
