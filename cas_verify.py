"""cas_verify.py -- re-verify the FriCAS / AXIOM answers in SymPy: the input
form returned by unparse is parsed and D(answer) - integrand evaluated at the
same rational points and precision as for the parallel method (charlwood.verify).

    python cas_verify.py fricas
    python cas_verify.py axiom
"""
import os, sys, json, re
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sympy as sp
from charlwood import BY_ID, CHARLWOOD, verify, x


def to_sympy(s):
    s = s.replace("^", "**").replace("%i", "I").replace("%pi", "pi").replace("%e", "E")
    X = sp.Symbol('x')
    e = sp.sympify(s, locals={'x': X})
    return e.subs(X, x)


def split_list(s):
    """top-level elements of a FriCAS/AXIOM list literal [a, b, ...]"""
    depth, cur, items = 0, "", []
    for ch in s[1:-1]:
        if ch in "([":
            depth += 1
        if ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            items.append(cur); cur = ""
        else:
            cur += ch
    items.append(cur)
    return items


def main(system):
    out = os.path.join(HERE, f"charlwood_{system}.json")
    d = json.load(open(out))
    for label, _ in CHARLWOOD:
        rec = d.get(label)
        if rec is None:
            continue
        s = rec.get("inputform")
        if rec["status"] in ("timeout", "error", "unevaluated integral") or not s:
            rec["sympy_check"] = None
            print(f"{label:<4} {rec['status']}")
            continue
        note = ""
        try:
            cands = split_list(s) if s.startswith("[") else [s]
            ok, errs = None, []
            for cand in cands:
                e = to_sympy(cand)
                ok, errs = verify(e, BY_ID[label])
                if ok:
                    if len(cands) > 1:
                        note = " (one of %d answers)" % len(cands)
                    break
            if ok is False:
                # a wrong sign of an algebraic kernel sqrt(r(x)) (branch choice)?
                e = to_sympy(cands[0])
                pows = [p for p in e.atoms(sp.Pow) if p.exp == sp.Rational(1, 2) and p.base.has(x)]
                for p in pows:
                    ok2, errs2 = verify(e.xreplace({p: -p}), BY_ID[label])
                    if ok2:
                        ok, errs, note = True, errs2, " (branch of %s)" % sp.sstr(p)
                        break
        except Exception as ex:
            ok, errs = None, [str(ex)]
        rec["sympy_check"] = ok
        rec["sympy_errors"] = [float(v) if not isinstance(v, str) else v for v in errs]
        rec["note"] = note
        rec["status"] = "integral" if ok else ("integral (unverified)" if ok is None else "WRONG")
        print(f"{label:<4} {rec['status']:<24} {note} {errs}")
    json.dump(d, open(out, "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1])
