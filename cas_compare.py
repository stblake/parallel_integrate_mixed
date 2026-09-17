"""cas_compare.py -- the fifty Charlwood integrals through the Risch--Trager--
Bronstein integrator of FriCAS and of AXIOM (one fresh process per integral,
so that a hang in one case cannot affect the others).

    python cas_compare.py fricas            # -> charlwood_fricas.json
    python cas_compare.py axiom             # -> charlwood_axiom.json
    python cas_compare.py fricas P3 A12     # a selection
    TIMEOUT=120 python cas_compare.py axiom   # per-integral limit (s; default 300)

For each integral the record holds the CAS's own timing line for the call
integrate(f, x), the result in TeX and in input form (unparse), whether the
result still contains an unevaluated integral(...), and a numeric check of
D(result) - f at rational points of the real domain, performed inside the CAS.
"""
import os, sys, re, json, subprocess, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sympy as sp
from charlwood import CHARLWOOD, BY_ID, real_points, x

SYSTEMS = {
    "fricas": {"cmd": ["fricas", "-nosman"], "quit": ")quit\n"},
    "axiom":  {"cmd": [os.path.expanduser("~/axiom/mnt/MACOSX/bin/AXIOMsys")], "quit": ")quit\ny\n"},
}


def to_cas(f):
    return str(f).replace("**", "^")


def script(f, pts):
    lines = [")set messages time on", ")set output length 500",
             f"f := {to_cas(f)}",
             "r := integrate(f, x)",
             ")set output tex on", ")set output algebra off", "r",
             ")set output tex off", ")set output algebra on",
             "unparse(r::InputForm)"]
    for p in pts:
        lines.append(f"complexNumeric(eval(D(r, x) - f, x, {sp.Rational(p)}), 20)")
    return "\n".join(lines) + "\n"


def run_one(system, label, f, timeout):
    sysd = SYSTEMS[system]
    pts = real_points(f, n=2)
    inp = script(f, pts) + sysd["quit"]
    rec = {"id": label, "integrand": to_cas(f), "system": system}
    t0 = time.time()
    try:
        pr = subprocess.run(sysd["cmd"], input=inp, capture_output=True, text=True, timeout=timeout)
        out = pr.stdout
    except subprocess.TimeoutExpired as e:
        out = (e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or ""))
        rec["status"] = "timeout"
    rec["wall"] = round(time.time() - t0, 2)
    rec["raw"] = out
    return parse(out, rec)


def parse(out, rec):
    """fill the record from the raw session transcript (value (2) is the
    integrate call, (4) the input form, (5), (6) the numeric checks)"""
    for k in ("cas_time", "cas_seconds", "tex", "inputform", "numeric", "detail"):
        rec.pop(k, None)
    if rec.get("status") != "timeout":
        rec.pop("status", None)
    # value blocks: "   (k)" labels; the integrate call is value (2)
    times = re.findall(r"Time: (.*?) sec", out)
    rec["times"] = times
    if "status" not in rec:
        blk2 = re.search(r"\n   \(2\)(.*?)Time: (.*?) sec", out, re.S)
        if blk2 is None:
            rec["status"] = "error"
            m = re.search(r">> (.*?)\n", out)
            rec["detail"] = m.group(1) if m else out[-600:]
        else:
            rec["cas_time"] = blk2.group(2).strip()
            m_total = re.search(r"= ([\d.]+)$", rec["cas_time"])
            rec["cas_seconds"] = float(m_total.group(1)) if m_total else None
            tex = re.search(r"\$\$(.*?)\$\$", out, re.S)
            rec["tex"] = tex.group(1).strip() if tex else None
            uf = re.search(r'\n   \(4\)\s*\n?\s*"(.*?)"\s*\n\s*Type: String', out, re.S)
            rec["inputform"] = re.sub(r"\s+", "", uf.group(1)) if uf else None
            nums = re.findall(r"\n   \((?:[5-9]|1\d)\)\s*\n?\s*(.*?)\n\s*Type: Complex", out, re.S)
            rec["numeric"] = [n.strip() for n in nums]
            text = rec["inputform"] or ""
            if "integral(" in text or (rec["tex"] and "\\int" in rec["tex"]):
                rec["status"] = "unevaluated integral"
            elif rec["inputform"] is None:
                rec["status"] = "no result parsed"
            else:
                def small(s):
                    s2 = s.replace(" ", "").replace("_", "")   # FriCAS groups digits with _
                    m = re.match(r"^(-?[\d.]+)(?:E(-?\d+))?", s2)
                    if not m:
                        return False
                    mant = float(m.group(1)); ex = int(m.group(2) or 0)
                    im = re.search(r"([+-][\d.]+)(?:E(-?\d+))?%i", s2)
                    imv = abs(float(im.group(1))) * 10 ** int(im.group(2) or 0) if im else 0.0
                    return abs(mant) * 10 ** ex < 1e-12 and imv < 1e-12
                if rec["numeric"] and all(small(n) for n in rec["numeric"]):
                    rec["status"] = "integral"
                elif not rec["numeric"]:
                    rec["status"] = "integral (unverified)"
                else:
                    rec["status"] = "WRONG?"
    return rec


def main(argv):
    system = argv[0]
    timeout = int(os.environ.get("TIMEOUT", "300"))
    out = os.environ.get("OUT", os.path.join(HERE, f"charlwood_{system}.json"))
    if "--reparse" in argv:                 # re-derive the statuses from the stored transcripts
        results = json.load(open(out))
        for label, rec in results.items():
            parse(rec["raw"], rec)
            print(f"{label:<4} {rec['status']:<24} {str(rec.get('cas_seconds')):>8}s")
        json.dump(results, open(out, "w"), indent=1)
        return
    sel = [a for a in argv[1:] if a in BY_ID] or [k for k, _ in CHARLWOOD]
    results = {}
    if os.path.exists(out) and len(sel) < len(CHARLWOOD):
        with open(out) as fh:
            results = json.load(fh)
    for label in sel:
        f = BY_ID[label]
        print(f"\n### {system} {label}: integrate({to_cas(f)}, x)", flush=True)
        rec = run_one(system, label, f, timeout)
        results[label] = rec
        print(f"--> {rec['status']}  CAS time {rec.get('cas_time')}  wall {rec['wall']}s", flush=True)
        if rec.get("inputform"):
            print("    " + rec["inputform"][:300], flush=True)
        if rec.get("numeric"):
            print("    numeric check:", rec["numeric"], flush=True)
        with open(out, "w") as fh:
            json.dump(results, fh, indent=1)
    print("\n" + "=" * 78)
    for label in sel:
        rec = results[label]
        print(f"{label:<4} {rec['status']:<24} {str(rec.get('cas_seconds')):>8}s  wall {rec['wall']:7.1f}s")
    print("=" * 78)


if __name__ == "__main__":
    main(sys.argv[1:])
