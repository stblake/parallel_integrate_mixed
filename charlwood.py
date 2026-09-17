"""charlwood.py -- the fifty integrals of

    K. Charlwood, Integration on computer algebra systems,
    Electronic J. Math. Technology 2 (2008) 291--301

(Problems 1--10 of the body and the forty of the Appendix) run through the
surface-form entry point of the SymPy implementation of Parallel Integration
over Simple Radical Extensions II (build_tower.integrate_surface, which
builds the tower and calls parallel_integrate_mixed).

    python charlwood.py                # all fifty, results to charlwood_results.json
    python charlwood.py P3 A12         # a selection
    TIMEOUT=120 python charlwood.py    # per-integral wall-clock limit (s; default 300)
    VERBOSE=1 python charlwood.py P5   # print the pipeline trace
    SPLIT_FIRST=1 python charlwood.py  # experiment: split specials over Fbar before parametrising a conic

Every returned integral is verified by differentiation at rational points
of the real domain of the integrand; every failure is recorded with the
status tuple or exception of the pipeline.
"""
import os, sys, time, signal, json, traceback, io, contextlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
# rnrad2 / weier (Parts I and III) live in the sibling elliptic directory
sys.path.insert(0, os.path.join(HERE, '..', 'older', 'elliptic'))

import sympy as sp
from sympy import sqrt, log, exp, sin, cos, tan, sec, asin, acos, atan, asec, Rational
from build_tower import integrate_surface, build_tower, TowerError, _substitute_back
from parallel_mixed import parallel_integrate_mixed

x = sp.Symbol('x', positive=True)

# ------------------------------------------------------------ the integrals
CHARLWOOD = [
    # Problems 1--10 (Charlwood 2008, Section 2)
    ("P1",  asin(x)*log(x)),
    ("P2",  x*asin(x)/sqrt(1 - x**2)),
    ("P3",  asin(sqrt(x + 1) - sqrt(x))),
    ("P4",  log(1 + x*sqrt(1 + x**2))),
    ("P5",  cos(x)**2/sqrt(cos(x)**4 + cos(x)**2 + 1)),
    ("P6",  tan(x)*sqrt(1 + tan(x)**4)),
    ("P7",  tan(x)/sqrt(sec(x)**3 + 1)),
    ("P8",  sqrt(tan(x)**2 + 2*tan(x) + 2)),
    ("P9",  sin(x)*atan(sqrt(sec(x) - 1))),
    ("P10", x**3*exp(asin(x))/sqrt(1 - x**2)),
    # Appendix: other integrals tested (row by row)
    ("A1",  x*log(1 + x**2)*log(x + sqrt(1 + x**2))/sqrt(1 + x**2)),
    ("A2",  atan(x + sqrt(1 - x**2))),
    ("A3",  x*atan(x + sqrt(1 - x**2))/sqrt(1 - x**2)),
    ("A4",  asin(x)/(1 + sqrt(1 - x**2))),
    ("A5",  log(x + sqrt(1 + x**2))/(1 - x**2)**Rational(3, 2)),
    ("A6",  asin(x)/(1 + x**2)**Rational(3, 2)),
    ("A7",  log(x + sqrt(x**2 - 1))/(1 + x**2)**Rational(3, 2)),
    ("A8",  log(x)/(x**2*sqrt(x**2 - 1))),
    ("A9",  sqrt(1 + x**3)/x),
    ("A10", x*log(x + sqrt(x**2 - 1))/sqrt(x**2 - 1)),
    ("A11", x**3*asin(x)/sqrt(1 - x**4)),
    ("A12", x**3*asec(x)/sqrt(x**4 - 1)),
    ("A13", x*atan(x)*log(x + sqrt(1 + x**2))/sqrt(1 + x**2)),
    ("A14", x*log(1 + sqrt(1 - x**2))/sqrt(1 - x**2)),
    ("A15", x*log(x + sqrt(1 + x**2))/sqrt(1 + x**2)),
    ("A16", x*log(x + sqrt(1 - x**2))/sqrt(1 - x**2)),
    ("A17", log(x)/(x**2*sqrt(1 - x**2))),
    ("A18", x*atan(x)/sqrt(1 + x**2)),
    ("A19", atan(x)/(x**2*sqrt(1 - x**2))),
    ("A20", x*atan(x)/sqrt(1 - x**2)),
    ("A21", atan(x)/(x**2*sqrt(1 + x**2))),
    ("A22", asin(x)/(x**2*sqrt(1 - x**2))),
    ("A23", x*log(x)/sqrt(x**2 - 1)),
    ("A24", log(x)/(x**2*sqrt(1 + x**2))),
    ("A25", x*asec(x)/sqrt(x**2 - 1)),
    ("A26", x*log(x)/sqrt(1 + x**2)),
    ("A27", sqrt(sin(x))/(1 + sin(x)**2)),
    ("A28", (1 + x**2)/((1 - x**2)*sqrt(1 + x**4))),
    ("A29", (1 - x**2)/((1 + x**2)*sqrt(1 + x**4))),
    ("A30", log(sin(x))/(1 + sin(x))),
    ("A31", log(sin(x))*sqrt(1 + sin(x))),
    ("A32", sec(x)/sqrt(sec(x)**4 - 1)),
    ("A33", tan(x)/sqrt(1 + tan(x)**4)),
    ("A34", sin(x)/sqrt(1 - sin(x)**6)),
    ("A35", sqrt(sqrt(sec(x) + 1) - sqrt(sec(x) - 1))),
    ("A36", x*log(x**2 + 1)*atan(x)**2),
    ("A37", atan(x*sqrt(1 + x**2))),
    ("A38", atan(sqrt(x + 1) - sqrt(x))),
    ("A39", asin(x*sqrt(1 - x**2))),
    ("A40", atan(x*sqrt(1 - x**2))),
]
BY_ID = dict(CHARLWOOD)

# ------------------------------------------------------------ verification
CANDIDATES = [Rational(1, 3), Rational(1, 2), Rational(2, 3), Rational(3, 2), 2, 3,
              Rational(1, 5), Rational(4, 5), Rational(5, 2), Rational(1, 7), 5]


def real_points(f, n=3):
    """rational points at which the integrand is real and finite"""
    pts = []
    for p in CANDIDATES:
        try:
            v = complex(sp.N(f.subs(x, p), 30))
        except (TypeError, ValueError, ZeroDivisionError):
            continue
        if abs(v.imag) < 1e-20 and abs(v) < 1e10:
            pts.append(p)
        if len(pts) >= n:
            break
    return pts


def verify(result, f, tol=1e-18):
    """|D(result) - f| at rational points of the real domain, 30 digits"""
    pts = real_points(f)
    if not pts:
        return None, []
    dr = sp.diff(result, x)
    errs = []
    for p in pts:
        try:
            v = complex(sp.N((dr - f).subs(x, p), 30))
        except (TypeError, ValueError, ZeroDivisionError):
            return False, errs
        errs.append(abs(v))
    return all(e < tol for e in errs), errs


class Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise Timeout()


def run_one(label, f, timeout=300, verbose=False):
    """build the tower, integrate, substitute back, verify; the verbose trace
    of the pipeline (prime classification, residues, candidates, system size)
    is kept in the record"""
    rec = {"id": label, "integrand": str(f)}
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    t0 = time.time()
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            try:
                T, fpair, back = build_tower(f, x, verbose=True)
                rec["tower"] = {"gens": [str(g) for g in T.gens],
                                "derivs": [[str(d[0]), str(d[1])] for d in T.derivs],
                                "q": str(T.q) if T.q is not None else None,
                                "integrand_pair": [str(fpair[0]), str(fpair[1])],
                                "back": [[str(a), str(b)] for a, b in back]}
                rec["t_tower"] = round(time.time() - t0, 2)
            except TowerError as e:
                rec["status"] = "tower error"
                rec["detail"] = str(e)
                raise _Done()
            res = parallel_integrate_mixed(fpair, T, verbose=True,
                                           split_first=os.environ.get("SPLIT_FIRST") == "1")
            rec["t_integrate"] = round(time.time() - t0 - rec["t_tower"], 2)
        if isinstance(res, sp.Basic):
            rec["result_tower"] = str(res)
            r = _substitute_back(res, back)
            ok, errs = verify(r, f)
            rec["status"] = "integral" if ok else ("integral (unverified)" if ok is None else "WRONG")
            rec["result"] = str(r)
            rec["latex"] = sp.latex(r)
            rec["errors"] = [float(e) for e in errs]
        else:
            rec["status"] = str(res[0])
            rec["detail"] = str(tuple(_substitute_back(r_, back) if isinstance(r_, sp.Basic) else r_
                                      for r_ in res[1:]))
    except _Done:
        pass
    except Timeout:
        rec["status"] = "timeout"
    except Exception as e:  # pragma: no cover
        rec["status"] = "exception"
        rec["detail"] = f"{type(e).__name__}: {e}"
        rec["traceback"] = traceback.format_exc()
    finally:
        signal.alarm(0)
    rec["trace"] = buf.getvalue()
    if verbose:
        print(rec["trace"])
    rec["time"] = round(time.time() - t0, 2)
    return rec


class _Done(Exception):
    pass


def main(argv):
    timeout = int(os.environ.get("TIMEOUT", "300"))
    verbose = os.environ.get("VERBOSE") == "1"
    out = os.environ.get("OUT", os.path.join(HERE, "charlwood_results.json"))
    sel = [a for a in argv if a in BY_ID] or [k for k, _ in CHARLWOOD]
    results = {}
    if os.path.exists(out) and len(sel) < len(CHARLWOOD):
        with open(out) as fh:
            results = json.load(fh)
    for label in sel:
        f = BY_ID[label]
        print(f"\n### {label}: int {f} dx", flush=True)
        rec = run_one(label, f, timeout=timeout, verbose=verbose)
        results[label] = rec
        print(f"--> {rec['status']}  ({rec['time']}s)", flush=True)
        if "result" in rec:
            print("    " + rec["result"][:400] + (" ..." if len(rec["result"]) > 400 else ""), flush=True)
        elif "detail" in rec:
            print("    " + rec["detail"][:400], flush=True)
        with open(out, "w") as fh:
            json.dump(results, fh, indent=1)
    print("\n" + "=" * 78)
    for label in sel:
        rec = results[label]
        print(f"{label:<4} {rec['status']:<32} {rec['time']:7.1f}s")
    print("=" * 78)
    n_ok = sum(1 for l in sel if results[l]["status"] == "integral")
    print(f"{n_ok}/{len(sel)} integrals returned and verified")


if __name__ == "__main__":
    main(sys.argv[1:])
