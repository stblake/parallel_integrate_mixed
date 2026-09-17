"""charlwood_report.py -- LaTeX table and number macros from the three result files

    charlwood_results.json   (charlwood.py:   parallel_mixed via build_tower)
    charlwood_fricas.json    (cas_compare.py fricas)
    charlwood_axiom.json     (cas_compare.py axiom)
    charlwood_results_splitfirst.json  (SPLIT_FIRST=1 charlwood.py A16 A1 A2 A3 P4,
                             the experiment of the assessment section; optional)

writes charlwood_table.tex (the summary table of the paper, with a totals
block at the foot) and charlwood_numbers.tex (the macros \tpm{P1}, \tfr{P1},
\tax{P1} for the seconds, \spm{P1}, \sfr{P1}, \sax{P1} for the status marks,
\npm, \nfr, \nax for the counts of verified integrals, \totpm, \meanpm, \medpm
(and \totfr ..., \totax ...) for the total, mean and median seconds of each
system over the times shown, \tsf{A1} for the seconds of the split-first
experiment), and prints a plain-text summary.
"""
import os, sys, json, statistics
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sympy as sp
from charlwood import CHARLWOOD, x

LATEX_OPTS = dict(inv_trig_style="full", ln_notation=True, fold_short_frac=True, fold_func_brackets=False)


def load(name):
    p = os.path.join(HERE, name)
    return json.load(open(p)) if os.path.exists(p) else {}


MARKS = {"integral": r"\checkmark", "integral (unverified)": r"\checkmark^{?}",
         "not elementary": r"\textsf{NE}", "failed": r"\textsf{F}",
         "timeout": r"\textsf{T}", "tower error": r"\textsf{TE}", "exception": r"\textsf{E}",
         "WRONG": r"\textsf{W}", "WRONG?": r"\textsf{W?}",
         "unevaluated integral": r"\textsf{U}", "error": r"\textsf{E}",
         "no result parsed": r"\textsf{?}",
         "needs torsion realisation (Parts I--II, milestone iii)": r"\textsf{F}"}

# the marks of the totals block, in order; \textsf{T} is always shown (the
# time limit is part of the protocol), the others when some system has one
LEGEND = [(r"\checkmark", "verified integrals"), (r"\textsf{NE}", "certificates of non-elementarity"),
          (r"\textsf{F}", "``failed''"), (r"\textsf{T}", "time limit reached"),
          (r"\textsf{TE}", "tower not built"), (r"\textsf{W}", "wrong answers"),
          (r"\textsf{U}", "unevaluated integrals"), (r"\textsf{E}", "errors")]
ALWAYS = {r"\textsf{T}"}


def mark(status):
    return MARKS.get(status, status)


def fmt_time(t):
    if t is None:
        return "--"
    if t < 0.05:
        return "$<0.1$"
    return f"{t:.1f}"


COMPACT = {
    "P1": r"\arcsin(x)\ln(x)", "P2": r"x\arcsin(x)/\sqrt{1-x^2}", "P3": r"\arcsin(\sqrt{x+1}-\sqrt x)",
    "P4": r"\ln(1+x\sqrt{1+x^2})", "P5": r"\cos^2(x)/\sqrt{\cos^4(x)+\cos^2(x)+1}", "P6": r"\tan(x)\sqrt{1+\tan^4(x)}",
    "P7": r"\tan(x)/\sqrt{\sec^3(x)+1}", "P8": r"\sqrt{\tan^2(x)+2\tan(x)+2}", "P9": r"\sin(x)\arctan(\sqrt{\sec(x)-1})",
    "P10": r"x^3e^{\arcsin(x)}/\sqrt{1-x^2}",
    "A1": r"x\ln(1+x^2)\ln(x+\sqrt{1+x^2})/\sqrt{1+x^2}", "A2": r"\arctan(x+\sqrt{1-x^2})",
    "A3": r"x\arctan(x+\sqrt{1-x^2})/\sqrt{1-x^2}", "A4": r"\arcsin(x)/(1+\sqrt{1-x^2})",
    "A5": r"\ln(x+\sqrt{1+x^2})/(1-x^2)^{3/2}", "A6": r"\arcsin(x)/(1+x^2)^{3/2}",
    "A7": r"\ln(x+\sqrt{x^2-1})/(1+x^2)^{3/2}", "A8": r"\ln(x)/(x^2\sqrt{x^2-1})", "A9": r"\sqrt{1+x^3}/x",
    "A10": r"x\ln(x+\sqrt{x^2-1})/\sqrt{x^2-1}", "A11": r"x^3\arcsin(x)/\sqrt{1-x^4}",
    "A12": r"x^3\operatorname{arcsec}(x)/\sqrt{x^4-1}", "A13": r"x\arctan(x)\ln(x+\sqrt{1+x^2})/\sqrt{1+x^2}",
    "A14": r"x\ln(1+\sqrt{1-x^2})/\sqrt{1-x^2}", "A15": r"x\ln(x+\sqrt{1+x^2})/\sqrt{1+x^2}",
    "A16": r"x\ln(x+\sqrt{1-x^2})/\sqrt{1-x^2}", "A17": r"\ln(x)/(x^2\sqrt{1-x^2})",
    "A18": r"x\arctan(x)/\sqrt{1+x^2}", "A19": r"\arctan(x)/(x^2\sqrt{1-x^2})", "A20": r"x\arctan(x)/\sqrt{1-x^2}",
    "A21": r"\arctan(x)/(x^2\sqrt{1+x^2})", "A22": r"\arcsin(x)/(x^2\sqrt{1-x^2})", "A23": r"x\ln(x)/\sqrt{x^2-1}",
    "A24": r"\ln(x)/(x^2\sqrt{1+x^2})", "A25": r"x\operatorname{arcsec}(x)/\sqrt{x^2-1}", "A26": r"x\ln(x)/\sqrt{1+x^2}",
    "A27": r"\sqrt{\sin(x)}/(1+\sin^2(x))", "A28": r"(1+x^2)/((1-x^2)\sqrt{1+x^4})",
    "A29": r"(1-x^2)/((1+x^2)\sqrt{1+x^4})", "A30": r"\ln(\sin(x))/(1+\sin(x))", "A31": r"\ln(\sin(x))\sqrt{1+\sin(x)}",
    "A32": r"\sec(x)/\sqrt{\sec^4(x)-1}", "A33": r"\tan(x)/\sqrt{1+\tan^4(x)}", "A34": r"\sin(x)/\sqrt{1-\sin^6(x)}",
    "A35": r"\sqrt{\sqrt{\sec(x)+1}-\sqrt{\sec(x)-1}}", "A36": r"x\ln(x^2+1)\arctan^2(x)",
    "A37": r"\arctan(x\sqrt{1+x^2})", "A38": r"\arctan(\sqrt{x+1}-\sqrt x)", "A39": r"\arcsin(x\sqrt{1-x^2})",
    "A40": r"\arctan(x\sqrt{1-x^2})",
}


def integrand_latex(f, label=None):
    if label in COMPACT:
        return COMPACT[label]
    return sp.latex(f, **LATEX_OPTS)


HEADER = (r"\multicolumn{1}{|c|}{} & \multicolumn{1}{c|}{integrand} & \multicolumn{2}{c|}{PM} & "
          r"\multicolumn{2}{c|}{FriCAS} & \multicolumn{2}{c|}{AXIOM}\\ \hline")


def main():
    py, fr, ax = load("charlwood_results.json"), load("charlwood_fricas.json"), load("charlwood_axiom.json")
    sf = load("charlwood_results_splitfirst.json")
    rows = []
    for label, f in CHARLWOOD:
        r = py.get(label, {}); g = fr.get(label, {}); a = ax.get(label, {})
        rows.append((label, integrand_latex(f, label),
                     mark(r.get("status", "?")), r.get("time"),
                     mark(g.get("status", "?")), g.get("cas_seconds") if g.get("status") != "timeout" else None,
                     mark(a.get("status", "?")), a.get("cas_seconds") if a.get("status") != "timeout" else None,
                     r.get("status"), g.get("status"), a.get("status")))
    # totals per system: counts of each mark, and the sum of the times shown
    systems = [(2, 3), (4, 5), (6, 7)]          # (mark column, time column) in rows
    counts = [{m: sum(1 for row in rows if row[mc] == m) for m, _ in LEGEND} for mc, _ in systems]
    shown = [[row[tc] for row in rows if row[tc] is not None] for _, tc in systems]
    totals = [sum(t) for t in shown]
    means = [statistics.mean(t) if t else None for t in shown]
    medians = [statistics.median(t) if t else None for t in shown]
    with open(os.path.join(HERE, "charlwood_table.tex"), "w") as fh:
        fh.write("% generated by charlwood_report.py\n")
        fh.write(r"\begingroup\small\setlength{\tabcolsep}{4pt}\setlength{\LTcapwidth}{\textwidth}" + "\n")
        fh.write(r"\begin{longtable}{|l|>{$}l<{$}|c@{\ }r|c@{\ }r|c@{\ }r|}" + "\n")
        fh.write(r"\caption{The fifty integrals of \cite{Charlwood08}: outcome and time in seconds "
                 r"for the parallel method (PM), FriCAS 1.3.6 and AXIOM (2014); "
                 r"Charlwood's $\theta$ is written $x$. $\checkmark$ an integral verified by differentiation, \textsf{NE} a certificate of non-elementarity, "
                 r"\textsf{F} ``failed'', \textsf{T} the 300-second limit, \textsf{TE} the tower could not be built, "
                 r"\textsf{W} a returned answer that fails the differentiation test, "
                 r"\textsf{U} an unevaluated integral in the answer, \textsf{E} an error. "
                 r"The last rows count the outcomes and give the total, the mean and the median of the times shown.}\label{tab:summary}\\" + "\n")
        fh.write(r"\hline" + "\n" + HEADER + "\n" + r"\endfirsthead" + "\n")
        fh.write(r"\multicolumn{8}{l}{Table~\ref{tab:summary} (continued)}\\[2pt]" + "\n")
        fh.write(r"\hline" + "\n" + HEADER + "\n" + r"\endhead" + "\n")
        fh.write(r"\hline\endfoot" + "\n" + r"\endlastfoot" + "\n")
        for (label, il, m1, t1, m2, t2, m3, t3, *_ ) in rows:
            if label == "A1":
                fh.write(r"\hline" + "\n")
            fh.write(f"{label} & {il} & ${m1}$ & {fmt_time(t1)} & ${m2}$ & {fmt_time(t2)} & ${m3}$ & {fmt_time(t3)}\\\\\n")
        fh.write(r"\hline" + "\n")
        for m, text in LEGEND:
            if m in ALWAYS or any(c[m] for c in counts):
                cells = " & ".join(r"\multicolumn{2}{c|}{%d}" % c[m] for c in counts)
                fh.write(r"\multicolumn{2}{|l|}{$%s$ %s} & %s\\" % (m, text, cells) + "\n")
        for text, vals in (("total time (s)", totals), ("mean time (s)", means), ("median time (s)", medians)):
            cells = " & ".join(r"\multicolumn{2}{c|}{%s}" % fmt_time(t) for t in vals)
            fh.write(r"\multicolumn{2}{|l|}{%s} & %s\\" % (text, cells) + "\n")
        fh.write(r"\hline" + "\n")
        fh.write(r"\end{longtable}" + "\n" + r"\endgroup" + "\n")
    # numbers as LaTeX macros: \tpm{P1}, \tfr{P1}, \tax{P1} (seconds), \spm{P1} ... (status marks)
    with open(os.path.join(HERE, "charlwood_numbers.tex"), "w") as fh:
        fh.write("% generated by charlwood_report.py\n")
        fh.write("\\makeatletter\n")
        for (label, il, m1, t1, m2, t2, m3, t3, s1, s2, s3) in rows:
            for tag, val in (("tpm", fmt_time(t1)), ("tfr", fmt_time(t2)), ("tax", fmt_time(t3)),
                             ("spm", m1), ("sfr", m2), ("sax", m3)):
                fh.write(f"\\expandafter\\def\\csname {tag}@{label}\\endcsname{{{val}}}\n")
        for label, r in sf.items():
            val = "$>300$" if r.get("status") == "timeout" else fmt_time(r.get("time"))
            fh.write(f"\\expandafter\\def\\csname tsf@{label}\\endcsname{{{val}}}\n")
        for tag in ("tpm", "tfr", "tax", "spm", "sfr", "sax", "tsf"):
            fh.write(f"\\newcommand{{\\{tag}}}[1]{{\\csname {tag}@#1\\endcsname}}\n")
        for name, d in (("npm", py), ("nfr", fr), ("nax", ax)):
            n = sum(1 for l, _ in CHARLWOOD if d.get(l, {}).get("status") == "integral")
            fh.write(f"\\newcommand{{\\{name}}}{{{n}}}\n")
        for suffix, tot, mean, med in zip(("pm", "fr", "ax"), totals, means, medians):
            fh.write(f"\\newcommand{{\\tot{suffix}}}{{{tot:.0f}}}\n")
            fh.write(f"\\newcommand{{\\mean{suffix}}}{{{fmt_time(mean)}}}\n")
            fh.write(f"\\newcommand{{\\med{suffix}}}{{{fmt_time(med)}}}\n")
        fh.write("\\makeatother\n")
    # plain summary
    print(f"{'id':<4} {'PM':<30} {'t':>7}   {'FriCAS':<22} {'t':>6}   {'AXIOM':<22} {'t':>6}")
    for (label, il, m1, t1, m2, t2, m3, t3, s1, s2, s3) in rows:
        print(f"{label:<4} {str(s1):<30} {str(t1):>7}   {str(s2):<22} {str(t2):>6}   {str(s3):<22} {str(t3):>6}")
    for (name, d), c, t in zip((("PM", py), ("FriCAS", fr), ("AXIOM", ax)), counts, totals):
        n = sum(1 for l, _ in CHARLWOOD if d.get(l, {}).get("status") == "integral")
        others = ", ".join(f"{m} {c[m]}" for m, _ in LEGEND if c[m] and m != r"\checkmark")
        print(f"{name}: {n}/{len(CHARLWOOD)} verified integrals; {others or 'nothing else'}; {t:.1f} s in all")


if __name__ == "__main__":
    main()
