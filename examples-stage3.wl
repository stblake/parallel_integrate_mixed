(* ::Package:: *)

(* examples-stage3.wl -- exercises the stage-3 mechanisms of ParallelMixed.wl:
   unit logands from the continued fraction of Sqrt[q], the non-torsion
   certificate by reduction modulo primes, and the holomorphic-remainder
   certificate with the exact bounds of Part I.  With stages 1-3 loaded this
   is the full benchmark suite of Section 10 of the paper.

     wolframscript -file examples-stage3.wl                                    *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "ParallelMixed.wl"}]];
Needs["ParallelMixed`"];

ClearAll[x, t];
results = {};


checkIntegral[I0_, surface_, subs_, var_] := Module[{Is = I0 /. subs},
  AllTrue[{3/2, 2, 7/3}, Abs[N[(D[Is, var] - surface) /. var -> #, 30]] < 10^-20 &]];

run[label_, f_, T_, expect_, OptionsPattern[{"Surface" -> None, "Subs" -> {}, "Var" -> x, "Verbose" -> False}]] :=
  Module[{r, ok, t0 = AbsoluteTime[], dt},
    Print["\n### ", label];
    r = ParallelIntegrateMixed[f, T, "Verbose" -> OptionValue["Verbose"]];
    dt = AbsoluteTime[] - t0;
    If[expect === "integral",
      ok = ! ListQ[r];
      If[ok && OptionValue["Surface"] =!= None,
        ok = checkIntegral[r, OptionValue["Surface"], OptionValue["Subs"], OptionValue["Var"]]];
      Print[r],
      ok = ListQ[r] && StringStartsQ[ToString[r[[1]]], expect];
      Print[r]];
    AppendTo[results, {label, expect, ok, dt}];
    Print["--> ", If[ok, "PASS", "FAIL"], "  (", NumberForm[dt, {4, 1}], "s)"]];

q = x^2 + 1;
ys = Sqrt[q];

(* 10.2: the unit x + y is invisible to residues and forced through the system *)
run["10.2 irreplaceable unit (t = exp y)", {0, (1 + x t)/q},
  Tower[{x, t}, {{1, 0}, {0, x t/q}}, q], "integral",
  "Surface" -> (1 + x Exp[ys])/ys, "Subs" -> {t -> Exp[ys]}, "Verbose" -> True];

(* 10.12 Cohen 1993: the whole integral is a unit of degree 8 *)
q71 = x^4 + 10 x^2 - 96 x - 71;
run["10.12 Cohen 1993 (unit of degree 8)", {0, x/q71}, Tower[{x}, {{1, 0}}, q71], "integral",
  "Surface" -> x/Sqrt[q71], "Verbose" -> True];

(* 10.12 the -72 variant: non-torsion certified mod p, then the exact bounds *)
run["10.12 Cohen's -72 variant: not elementary (non-torsion mod p + exact bounds)",
  {0, x/(x^4 + 10 x^2 - 96 x - 72)}, Tower[{x}, {{1, 0}}, x^4 + 10 x^2 - 96 x - 72],
  "not elementary", "Verbose" -> True];

(* 10.13 Schultz 2015: genus 2, unit of degree 29 *)
q6 = x^6 + 4 x^5 + 6 x^4 - 12 x^3 + 33 x^2 - 16 x;
run["10.13 Schultz 2015 (genus 2, unit of degree 29)", {0, (29 x^2 + 18 x - 3)/q6},
  Tower[{x}, {{1, 0}}, q6], "integral", "Surface" -> (29 x^2 + 18 x - 3)/Sqrt[q6], "Verbose" -> True];

(* 10.15 Chebyshev: Hermite part + norm-search residues + order-5 unit *)
q4 = x^4 + 4 x^3 + 2 x^2 + 1;
N4 = 2 x^6 + 4 x^5 + 7 x^4 - 3 x^3 - x^2 - 8 x - 8;
run["10.15 Chebyshev (Davenport Ex. 5): all three mechanisms", {0, N4/((2 x^2 - 1)^2 q4)},
  Tower[{x}, {{1, 0}}, q4], "integral", "Surface" -> N4/((2 x^2 - 1)^2 Sqrt[q4]), "Verbose" -> True];

(* the holomorphic-remainder certificate: 3-torsion divisor, remainder dx/(3y) *)
run["9.2(b) certified: dx/((x-2) sqrt(x^3+1)) (holomorphic remainder)", {0, 1/((x - 2) (x^3 + 1))},
  Tower[{x}, {{1, 0}}, x^3 + 1], "not elementary", "Verbose" -> True];

(* torus over the logarithmic tower: split residues by norm search, unit t + y *)
qt = t^2 + 1;
yt = Sqrt[Log[x]^2 + 1];
run["regression: torus over the logarithmic tower", {5/(2 x t), (4 t^3 + 3 t + 1)/(2 x t qt)},
  Tower[{x, t}, {{1, 0}, {1/x, 0}}, qt], "integral",
  "Surface" -> (4 Log[x]^3 + 3 Log[x] + 1 + 5 yt)/(2 x Log[x] yt), "Subs" -> {t -> Log[x]}, "Verbose" -> True];

Print["\n", StringRepeat["=", 78]];
Do[Print[PaddedForm[r[[1]], 70], "  ", r[[2]], "  ", If[r[[3]], "PASS", "FAIL"], "  ", NumberForm[r[[4]], {5, 1}], "s"], {r, results}];
Print[StringRepeat["=", 78]];
Print[Count[results, {_, _, True, _}], "/", Length[results], " passed"];

(* S'-units over a special prime (surface form) *)
Print["\n### S18 int log(x) arcsin(x): needs the S'-unit 1 - sqrt(1-x^2) over the special x"];
r18 = ParallelIntegrateMixed[Log[x] ArcSin[x], x, "Verbose" -> True, "Verify" -> True];
Print[r18];
Print["--> ", If[! ListQ[r18] && AllTrue[{1/3, 1/2}, Abs[N[(D[r18, x] - Log[x] ArcSin[x]) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* Euler parametrisation of a conic when a second radical is demanded *)
Print["\n### S19 int arcsin(sqrt(x+1) - sqrt(x)): conic y^2 = u^2 + 1 parametrised by w = y - u"];
r19 = ParallelIntegrateMixed[ArcSin[Sqrt[x + 1] - Sqrt[x]], x, "Verbose" -> True, "Verify" -> True];
Print[r19];
Print["--> ", If[! ListQ[r19] && r19 =!= $Failed && AllTrue[{1/3, 2}, Abs[N[(D[r19, x] - ArcSin[Sqrt[x + 1] - Sqrt[x]]) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* trigonometric integrands: automatic tangent conversion, quartic -> cubic model, Miller S'-units *)
Print["\n### S20 int cos^2 x / sqrt(cos^4 x + cos^2 x + 1): t = tan x, then the cubic model of t^4+3t^2+3"];
f20 = Cos[x]^2/Sqrt[Cos[x]^4 + Cos[x]^2 + 1];
r20 = ParallelIntegrateMixed[f20, x, "Verbose" -> True, "Verify" -> True];
Print[r20];
Print["--> ", If[! ListQ[r20] && r20 =!= $Failed && AllTrue[{1/3, 1}, Abs[N[(D[r20, x] - f20) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];
Print["\n### S21 int sin x / (1 + cos x)  (odd: half-angle t = tan(x/2))"];
r21 = ParallelIntegrateMixed[Sin[x]/(1 + Cos[x]), x, "Verbose" -> True, "Verify" -> True]; Print[r21];
Print["\n### S22 int sinh^2 x  (even hyperbolic: t = tanh x)"];
r22 = ParallelIntegrateMixed[Sinh[x]^2, x, "Verbose" -> True, "Verify" -> True]; Print[r22];

(* parity rules: odd in sin -> u = cos x (Charlwood) *)
Print["\n### S23 int tan(x)/sqrt(1+sec^3 x): odd in sin, u = cos x, degree-3 unit"];
f23 = Tan[x]/Sqrt[1 + Sec[x]^3];
r23 = ParallelIntegrateMixed[f23, x, "Verbose" -> True, "Verify" -> True]; Print[r23];
Print["--> ", If[! ListQ[r23] && r23 =!= $Failed && AllTrue[{1/3, 1}, Abs[N[(D[r23, x] - f23) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];
Print["\n### S24 int tan(x) sqrt(1+tan^4 x): even, t = tan x (radical over the tangent: no v_oo certificate)"];
f24 = Tan[x] Sqrt[1 + Tan[x]^4];
r24 = ParallelIntegrateMixed[f24, x, "Verbose" -> True, "Verify" -> True]; Print[r24];
Print["--> ", If[! ListQ[r24] && r24 =!= $Failed && AllTrue[{1/3, 1}, Abs[N[(D[r24, x] - f24) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* conic parametrised away (genus 0): the S'-units over the special x^4-x^2+1 have rank 9 on the curve *)
Print["\n### S25 int arctan(x + sqrt(1-x^2)): conic y^2 = 1-x^2 parametrised by w = (y-1)/x"];
f25 = ArcTan[x + Sqrt[1 - x^2]];
r25 = ParallelIntegrateMixed[f25, x, "Verbose" -> True, "Verify" -> True]; Print[Short[r25, 6]];
Print["--> ", If[! ListQ[r25] && r25 =!= $Failed && AllTrue[{1/3, 1/2}, Abs[N[(D[r25, x] - f25) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* conic parametrised away (genus 0): the S'-units over the special x^4-x^2+1 have rank 9 on the curve *)
Print["\n### S25 int arctan(x + sqrt(1-x^2)): conic y^2 = 1-x^2 parametrised by w = (y-1)/x"];
f25 = ArcTan[x + Sqrt[1 - x^2]];
r25 = ParallelIntegrateMixed[f25, x, "Verbose" -> True, "Verify" -> True]; Print[Short[r25, 6]];
Print["--> ", If[! ListQ[r25] && r25 =!= $Failed && AllTrue[{1/3, 1/2}, Abs[N[(D[r25, x] - f25) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* two conics: the one from arcsin's derivative is parametrised through a rational point *)
Print["\n### S26 int arcsin(x)/(1+x^2)^(3/2): y^2 = 1-x^2 parametrised via (0,1); the other radical becomes a genus-1 quartic"];
f26 = ArcSin[x]/(1 + x^2)^(3/2);
r26 = ParallelIntegrateMixed[f26, x, "Verbose" -> True, "Verify" -> True]; Print[Short[r26, 6]];
Print["--> ", If[! ListQ[r26] && r26 =!= $Failed && AllTrue[{1/3, 1/2}, Abs[N[(D[r26, x] - f26) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* Euler parametrisation sign: the large root w = sqrt(x^2-1) + x is positive on x > 1 *)
Print["\n### S27 int log(x+sqrt(x^2-1))/(1+x^2)^(3/2): checked on x > 1 (the natural real domain)"];
f27 = Log[x + Sqrt[x^2 - 1]]/(1 + x^2)^(3/2);
r27 = ParallelIntegrateMixed[f27, x, "Verbose" -> True]; Print[Short[r27, 6]];
Print["--> ", If[! ListQ[r27] && r27 =!= $Failed && AllTrue[{3/2, 2, 3}, Abs[N[(D[r27, x] - f27) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* the sign of a square-root normalisation is decided at a sample point of the real domain *)
Print["\n### S28 int x^3 arcsin(x)/sqrt(1-x^4): sqrt(1-x^4) -> (1-w^2) sqrt(...)/(1+w^2)^2 with the sign fixed on 0<x<1"];
f28 = x^3 ArcSin[x]/Sqrt[1 - x^4];
r28 = ParallelIntegrateMixed[f28, x, "Verbose" -> True]; Print[Short[r28, 6]];
Print["--> ", If[! ListQ[r28] && r28 =!= $Failed && AllTrue[{1/3, 1/2}, Abs[N[(D[r28, x] - f28) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];

(* every elementary inverse function as a generator; general powers as Exp[b Log[a]] *)
Print["\n### S29 int x^3 arcsec(x)/sqrt(x^4-1)"];
f29 = x^3 ArcSec[x]/Sqrt[x^4 - 1];
r29 = ParallelIntegrateMixed[f29, x, "Verbose" -> True]; Print[Short[r29, 6]];
Print["--> ", If[! ListQ[r29] && r29 =!= $Failed && AllTrue[{3/2, 2}, Abs[N[(D[r29, x] - f29) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];
Do[With[{ff = g}, Print["\n### S30 int ", ff]; With[{rr = ParallelIntegrateMixed[ff, x, "Verify" -> True]}, Print[rr]]],
  {g, {ArcSec[x], ArcCsc[x], ArcCot[x], ArcCoth[x], ArcSech[x], ArcCsch[x], x^x (1 + Log[x])}}];

(* residues at a prime of degree 8 (Charlwood A27): the residue polynomial in
   the residue field K[u]/(u^8 + 6 u^4 + 1), residue classes (prime, sheet
   polynomial), realisation by Hensel lifting and linear algebra over Q(i) *)
Print["\n### S31 int sqrt(sin x)/(1+sin^2 x): residues at the degree-8 prime u^8+6u^4+1 in the residue field"];
f31 = Sqrt[Sin[x]]/(1 + Sin[x]^2);
r31 = ParallelIntegrateMixed[f31, x, "Verbose" -> True]; Print[Short[r31, 6]];
Print["--> ", If[! ListQ[r31] && r31 =!= $Failed && AllTrue[{1/3, 3/2, 5/2}, Abs[N[(D[r31, x] - f31) /. x -> #, 30]] < 10^-20 &], "PASS", "FAIL"]];


(* radicals of degree m >= 3 (elements on the Trager basis w_i = y^i/E_i):
   unit logands from the divisor search at the places at infinity, residue
   classes in the residue field with the m x m norm, realisation by Hensel
   lifting and linear algebra with the pole orders at infinity distributed *)
runM[label_, f_, expect_: "integral"] := Module[{r, ok, t0 = AbsoluteTime[], dt},
  Print["\n### ", label];
  r = ParallelIntegrateMixed[f, x];
  dt = AbsoluteTime[] - t0;
  If[expect === "integral",
    ok = ! ListQ[r] && r =!= $Failed && AllTrue[{3/2, 2, 7/3}, Abs[N[(D[r, x] - f) /. x -> #, 30]] < 10^-18 &];
    Print[Short[r, 6]],
    ok = ListQ[r] && StringStartsQ[ToString[r[[1]]], expect];
    Print[r]];
  AppendTo[results, {label, expect, ok, dt}];
  Print["--> ", If[ok, "PASS", "FAIL"], "  (", NumberForm[dt, {4, 1}], "s)"]];
runM["M1  1/(x^3-1)^(1/3)  (Fermat cubic: units at the three places at infinity)", 1/(x^3 - 1)^(1/3)];
runM["M2  1/(x (x^3+1)^(1/3))  (residue classes over x, 3-torsion, logands y - zeta)", 1/(x (x^3 + 1)^(1/3))];
runM["M3  1/(x (x^2-1)^(1/3))  (one place at infinity, 2-torsion classes)", 1/(x (x^2 - 1)^(1/3))];
runM["M4  x^2 Log[x]/(x^3+1)^(2/3) + (x^3+1)^(1/3)/x  (log above the cube root)", x^2 Log[x]/(x^3 + 1)^(2/3) + (x^3 + 1)^(1/3)/x];
runM["M5  1/(x (x^4+1)^(1/4))  (m = 4, residue classes over Q(i))", 1/(x (x^4 + 1)^(1/4))];
runM["M6  1/(x^4+1)^(1/4)  (m = 4, units at the four places at infinity)", 1/(x^4 + 1)^(1/4)];
runM["M7  x/(x^3-1)^(1/3): not elementary, honest 'failed'", x/(x^3 - 1)^(1/3), "failed"];

Print["\n", StringRepeat["=", 78]];
Do[Print[r[[1]], "  ", r[[2]], "  ", If[r[[3]], "PASS", "FAIL"], "  ", NumberForm[r[[4]], {6, 1}], "s"], {r, results}];
Print[StringRepeat["=", 78]];
Print[Count[results, {_, _, True, _}], "/", Length[results], " passed"];
