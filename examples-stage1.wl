(* ::Package:: *)

(* examples-stage1.wl -- runs the Section 10 examples that stage 1 of the port
   covers, in the order of examples.py, and checks every returned integral by
   differentiating the surface expression.

     wolframscript -file examples-stage1.wl                                    *)

Get[FileNameJoin[{DirectoryName[$InputFileName], "ParallelMixed.wl"}]];
Needs["ParallelMixed`"];

ClearAll[x, t, u];
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
tl = Log[x + ys];

run["10.1 flagship: int log(x+sqrt(x^2+1))", {t, 0},
  Tower[{x, t}, {{1, 0}, {0, 1/q}}, q], "integral", "Surface" -> tl, "Subs" -> {t -> tl}];

run["10.2 irreplaceable unit (t = exp y): needs units (stage 3)", {0, (1 + x t)/q},
  Tower[{x, t}, {{1, 0}, {0, x t/q}}, q], "failed"];

run["10.3 moving prime: not elementary", {1/(x t), 0},
  Tower[{x, t}, {{1, 0}, {0, 1/q}}, q], "not elementary", "Verbose" -> True];

run["10.4 Bronstein (E): not elementary", {t^2/(1 + t^2), 1/(1 + t^2)},
  Tower[{x, t}, {{1, 0}, {1/(2 x t), 0}}, t^2 + t], "not elementary", "Verbose" -> True];

run["10.5 exp(sqrt x) (flattened)", {t, 0},
  Tower[{u, t}, {{1/(2 u), 0}, {t/(2 u), 0}}], "integral",
  "Surface" -> Exp[Sqrt[x]], "Subs" -> {u -> Sqrt[x], t -> Exp[Sqrt[x]]}];

run["10.6 tan(sqrt x)/sqrt x (flattened)", {t/u, 0},
  Tower[{u, t}, {{1/(2 u), 0}, {(1 + t^2)/(2 u), 0}}], "integral",
  "Surface" -> Tan[Sqrt[x]]/Sqrt[x], "Subs" -> {u -> Sqrt[x], t -> Tan[Sqrt[x]]}, "Verbose" -> True];

run["10.7 tan over the curve (elementary instance)", {x (1 + t^2), 3 x t/q},
  Tower[{x, t}, {{1, 0}, {0, x (1 + t^2)/q}}, q], "integral",
  "Surface" -> x (1 + Tan[ys]^2) + 3 x Tan[ys]/ys, "Subs" -> {t -> Tan[ys]}];

run["10.8 curve-split moving logands",
  {-(1 + 5 x)/(t^2 - x^2 - 1), (t^3 + (4 + x - x^2) t)/(q (t^2 - x^2 - 1))},
  Tower[{x, t}, {{1, 0}, {0, 1/q}}, q], "integral",
  "Surface" -> (tl^3 + (4 + x - x^2) tl - (1 + 5 x) ys)/(ys (tl^2 - x^2 - 1)),
  "Subs" -> {t -> tl}, "Verbose" -> True];

u14 = Sqrt[x + Log[x]];
run["10.9 tutorial Ex 14 (flattened)", {(x + 1)/(x u) + (2 x u + x + 1)/(x u (x + u)), 0},
  Tower[{x, u}, {{1, 0}, {(x + 1)/(2 x u), 0}}], "integral",
  "Surface" -> ((x^2 + 2 x + 1) u14 + (3 x + 1) Log[x] + 3 x^2 + x)/((x Log[x] + x^2) u14 + x^2 Log[x] + x^3),
  "Subs" -> {u -> u14}];

u15 = (x + Exp[x])^(1/3);
run["10.10 tutorial Ex 15 (flattened)", {((2 x^2 + 3 x) u^3 + 3 u + 2 x^2 - 2 x^3)/(x u), 0},
  Tower[{x, u}, {{1, 0}, {(u^3 - x + 1)/(3 u^2), 0}}], "integral",
  "Surface" -> (3 u15 + (2 x^2 + 3 x) Exp[x] + 5 x^2)/(x u15), "Subs" -> {u -> u15}];

Tj = Tower[{x, u}, {{1, 0}, {(x + 1)/(2 x u), 0}}];
run["10.11 JSC90 p.134", {(x + 1)/(x u^3), 0}, Tj, "integral",
  "Surface" -> (x + 1)/((x Log[x] + x^2) u14), "Subs" -> {u -> u14}, "Verbose" -> True];
run["10.11 JSC90 p.147 as printed (x^2+x+1): not elementary",
  {Cancel[((x^2 + x + 1) u + (3 x + 1) (u^2 - x) + 3 x^2 + x)/((x (u^2 - x) + x^2) u + x^2 (u^2 - x) + x^3)], 0},
  Tj, "not elementary", "Verbose" -> True];
run["10.11 JSC90 p.147 corrected, lowest terms", {Cancel[((x + 1)^2 + (3 x + 1) u)/(x u (u + x))], 0},
  Tj, "integral", "Surface" -> ((x + 1)^2 + (3 x + 1) u14)/(x u14 (u14 + x)), "Subs" -> {u -> u14}, "Verbose" -> True];

Print["\n", StringRepeat["=", 78]];
Do[Print[PaddedForm[r[[1]], 62], "  ", r[[2]], "  ", If[r[[3]], "PASS", "FAIL"], "  ", NumberForm[r[[4]], {5, 1}], "s"], {r, results}];
Print[StringRepeat["=", 78]];
Print[Count[results, {_, _, True, _}], "/", Length[results], " passed"];

(* ---------------------------------------------------------------- surface form *)
Print["\n\n=== surface-form entry point: ParallelIntegrateMixed[integrand, x] ==="];
surfaceResults = {};
runS[label_, integrand_, expect_, verbose_: False] := Module[{r, ok, t0 = AbsoluteTime[]},
  Print["\n### ", label];
  r = ParallelIntegrateMixed[integrand, x, "Verbose" -> verbose, "Verify" -> True];
  Print[r];
  ok = If[expect === "integral",
    ! ListQ[r] && r =!= $Failed && AllTrue[{3/2, 2, 7/3}, Abs[N[(D[r, x] - integrand) /. x -> #, 30]] < 10^-20 &],
    ListQ[r] && StringStartsQ[ToString[r[[1]]], expect]];
  AppendTo[surfaceResults, {label, ok}];
  Print["--> ", If[ok, "PASS", "FAIL"], "  (", NumberForm[AbsoluteTime[] - t0, {4, 1}], "s)"]];

runS["S1  int log(x + sqrt(x^2+1))", Log[x + Sqrt[x^2 + 1]], "integral", True];
runS["S2  int exp(sqrt x)", Exp[Sqrt[x]], "integral"];
runS["S3  int tan(sqrt x)/sqrt x", Tan[Sqrt[x]]/Sqrt[x], "integral"];
runS["S4  int (x(1+tan^2 y) + 3 x tan y / y), y = sqrt(x^2+1)",
  x (1 + Tan[Sqrt[x^2 + 1]]^2) + 3 x Tan[Sqrt[x^2 + 1]]/Sqrt[x^2 + 1], "integral", True];
runS["S5  Bronstein Ex 14", ((x + 1)^2 Sqrt[x + Log[x]] + (3 x + 1) Log[x] + 3 x^2 + x)/((x Log[x] + x^2) Sqrt[x + Log[x]] + x^2 Log[x] + x^3), "integral"];
runS["S6  Bronstein Ex 15", (3 (x + Exp[x])^(1/3) + (2 x^2 + 3 x) Exp[x] + 5 x^2)/(x (x + Exp[x])^(1/3)), "integral"];
runS["S7  JSC90 p.134", (x + 1)/((x Log[x] + x^2) Sqrt[x + Log[x]]), "integral"];
runS["S8  Bronstein (E), nested radical: not elementary", (Log[x] + Sqrt[Log[x] + Sqrt[Log[x]]])/(1 + Log[x]), "not elementary", True];
runS["S9  moving prime: not elementary", 1/(x Log[x + Sqrt[x^2 + 1]]), "not elementary"];

Print["\n", StringRepeat["=", 78]];
Do[Print[PaddedForm[r[[1]], 62], "  ", If[r[[2]], "PASS", "FAIL"]], {r, surfaceResults}];
Print[Count[surfaceResults, {_, True}], "/", Length[surfaceResults], " surface-form tests passed"];

(* ---------------------------------------------------- specials over Fbar *)
Print["\n=== specials split over the algebraic closure ==="];
runS["S10 int sqrt(tan x)  (specials 1+u^4 split into four linear factors)", Sqrt[Tan[x]], "integral", True];
runS["S11 int sqrt(log x): not elementary, honest 'failed' (no certificate class covers it)", Sqrt[Log[x]], "failed"];
runS["S12 int exp(x^2): not elementary, honest 'failed'", Exp[x^2], "failed"];

(* ------------------------------------------- inverse functions as primitives *)
Print["\n=== ArcTan / ArcSin generators (previously mis-handled as opaque atoms) ==="];
runS["S13 int arctan(x)/sqrt(x)", ArcTan[x]/Sqrt[x], "integral", True];
runS["S14 int arctan(sqrt x) = (x+1) arctan(sqrt x) - sqrt x", ArcTan[Sqrt[x]], "integral", True];
runS["S15 int arcsin(x) = x arcsin(x) + sqrt(1-x^2)  (radical introduced by the derivative)", ArcSin[x], "integral", True];
runS["S16 int x arctan(x)", x ArcTan[x], "integral"];
Print["\n### S17 Sin[x] is rejected with a message (not a monomial):"];
Print[ParallelIntegrateMixed[Sin[x], x]];
