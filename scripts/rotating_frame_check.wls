#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Problem 10.1 of manuscript/main.tex --- the synchronously rotating frame.
   Wolfram Language.  Written 2026-09-14.

   Theorem 3.3 and everything after it assume theta0 constant.  Here theta0 = theta0(t).
   The stator fields then carry an explicit time dependence, so the problem lives on
   R x Q with the extended frame  {v0 = d/dt, v1, ..., v7}.  This script answers the
   three questions the problem asks, in order.

     R1  the structure functions of the extended frame;
     R2  when they are constant (= when the extended frame spans a Lie algebra);
     R3  which algebra it is, and which group acts on R x Q;
     R4  whether the inductance metric still has the constant array (7.2);
     R5  the equations of motion, derived twice and compared --- once from the extended
         Hamel equation, once from the Euler-Lagrange equations in the abc coordinates;
     R6  comparison with Krause's arbitrary-reference-frame model;
     R7  the Euler-Poincare form, and the consistency of the eighth equation.

   CONVENTIONS, taken from the manuscript so the signs match:
     c^k_ij = <alpha^k, [v_i, v_j]>                                    (Remark 3.5)
     Hamel:  d/dt(dl/dxi^j) - c^k_ij xi^i dl/dxi^k - v_j[l] = f_j      (7.1)
     K(beta) is the array (3.1); stator uses K(theta0), rotor K(theta0 - theta).
     The rotor quantities are the REFERRED ones, so the mutual inductance is Lms
     throughout and the rotor leakage carries a^2, as in eq. (2.4).

   Every line printed with "count:" must read 0.
*)

Off[Solve::ifun];
line[] := Print[StringRepeat["-", 78]];
z[e_] := FullSimplify[TrigReduce[Expand[e]]];
cnt[b_] := If[TrueQ[b], 0, 1];

(* ============================================================ *)
(* R1  the extended frame and its structure functions            *)
(* ============================================================ *)
line[]; Print["R1  THE EXTENDED FRAME ON R x Q"]; line[];

ext = {tt, qsa, qsb, qsc, qra, qrb, qrc, th};
K[b_] := (2/3) {{Cos[b], Cos[b - 2 Pi/3], Cos[b + 2 Pi/3]},
                {Sin[b], Sin[b - 2 Pi/3], Sin[b + 2 Pi/3]},
                {1/2, 1/2, 1/2}};
b0 = th0[tt];

(* rows of FM are v0, v1, ..., v7 in the coordinate basis of ext *)
FM = Join[
  {UnitVector[8, 1]},
  Table[Join[{0}, K[b0][[i]], {0, 0, 0}, {0}], {i, 3}],
  Table[Join[{0}, {0, 0, 0}, K[b0 - th][[i]], {0}], {i, 3}],
  {UnitVector[8, 8]}];
Print["frame matrix is invertible, det = ", z[Det[FM]]];

brk[X_, Y_] := Table[Sum[X[[b]] D[Y[[a]], ext[[b]]] - Y[[b]] D[X[[a]], ext[[b]]],
    {b, 8}], {a, 8}];
inFrame[X_] := z /@ LinearSolve[Transpose[FM], X];

(* c[[i+1, j+1, k+1]] = c^k_ij, indices running 0..7 *)
cs = Table[inFrame[brk[FM[[i]], FM[[j]]]], {i, 8}, {j, 8}];
nzc = {};
Do[If[cs[[i, j, k]] =!= 0,
   AppendTo[nzc, {i - 1, j - 1, k - 1} -> cs[[i, j, k]]]], {i, 8}, {j, 8}, {k, 8}];
Print["non-vanishing structure functions c^k_ij, listed as {i,j,k} -> c:"];
Do[Print["    ", p], {p, nzc}];
Print["R1  count: structure functions involving v3 or v6 (indices 3, 6) = ",
  Count[nzc, p_ /; IntersectionQ[{3, 6}, First[p]]]];
Print["R1  count: departures of the seven-field block from Theorem 3.3 = ",
  cnt[And[z[cs[[5, 8, 6]] + 1] === 0, z[cs[[6, 8, 5]] - 1] === 0,
     Length[Select[nzc, FreeQ[First[#], 0] &]] === 4]]];

(* ============================================================ *)
(* R2  when do they close on a Lie algebra                       *)
(* ============================================================ *)
line[]; Print["R2  CONSTANCY OF THE STRUCTURE FUNCTIONS"]; line[];
allc = Union[Last /@ nzc];
Print["the set of values taken by the structure functions: ", allc];
Print["R2  count: values depending on a configuration variable of Q = ",
  Count[allc, e_ /; ! FreeQ[e, qsa | qra | th]]];
Print["R2  the only non-constant value is the frame rate; d/dt of each value:"];
Do[Print["    d/dt(", e, ") = ", D[e, tt]], {e, allc}];
Print["R2  count: values whose time derivative fails to vanish when theta0'' = 0 = ",
  Count[allc, e_ /; z[D[e, tt] /. Derivative[2][th0][tt] -> 0] =!= 0]];

(* from here on the frame rotates uniformly *)
syn = {Derivative[1][th0][tt] -> w, th0[tt] -> w tt + b00};
csw = z[cs /. syn];
Print["R2  under theta0 = w t + b00 the structure constants are: ",
  Union[DeleteCases[Flatten[csw], 0]]];

(* ============================================================ *)
(* R3  which Lie algebra                                         *)
(* ============================================================ *)
line[]; Print["R3  THE EXTENDED ALGEBRA"]; line[];
(* abstract 8-dim algebra with these constants; basis index 1..8 <-> v0..v7 *)
brA[x_, y_] := Table[Sum[x[[i]] y[[j]] csw[[i, j, k]], {i, 8}, {j, 8}], {k, 8}];
bas = IdentityMatrix[8];
jac = Flatten[Table[
   z[brA[bas[[i]], brA[bas[[j]], bas[[k]]]] + brA[bas[[j]], brA[bas[[k]], bas[[i]]]] +
     brA[bas[[k]], brA[bas[[i]], bas[[j]]]]], {i, 8}, {j, 8}, {k, 8}]];
Print["R3  count: Jacobi identity failures = ", Count[jac, e_ /; e =!= 0]];

centre = Select[Range[8],
   And @@ Table[z[brA[bas[[#]], bas[[j]]]] === Table[0, 8], {j, 8}] &];
Print["R3  centre of the extended algebra = ", (# - 1) & /@ centre, "  (as v-indices)"];
derv = DeleteCases[Flatten[Table[brA[bas[[i]], bas[[j]]], {i, 8}, {j, 8}], 1],
   v_ /; v === Table[0, 8]];
Print["R3  derived algebra: dimension ", MatrixRank[derv /. w -> 1],
  ", spanned by the v-directions ",
  Union[Flatten[Table[If[derv[[i, j]] =!= 0, j - 1, Nothing],
     {i, Length[derv]}, {j, 8}]]]];

(* the explicit splitting: A = -(v0 + w v7)/w,  B = v7 *)
A8 = -(bas[[1]] + w bas[[8]])/w;
B8 = bas[[8]];
P1 = bas[[2]]; P2 = bas[[3]];   (* v1, v2 *)
Q1 = bas[[5]]; Q2 = bas[[6]];   (* v4, v5 *)
Z1 = bas[[4]]; Z2 = bas[[7]];   (* v3, v6 *)
tests = {
  "[A,v1] - v2" -> brA[A8, P1] - P2,
  "[A,v2] + v1" -> brA[A8, P2] + P1,
  "[v1,v2]" -> brA[P1, P2],
  "[B,v4] - v5" -> brA[B8, Q1] - Q2,
  "[B,v5] + v4" -> brA[B8, Q2] + Q1,
  "[v4,v5]" -> brA[Q1, Q2],
  "[A,B]" -> brA[A8, B8],
  "[A,v4]" -> brA[A8, Q1], "[A,v5]" -> brA[A8, Q2],
  "[B,v1]" -> brA[B8, P1], "[B,v2]" -> brA[B8, P2],
  "[v1,v4]" -> brA[P1, Q1], "[v1,v5]" -> brA[P1, Q2],
  "[v2,v4]" -> brA[P2, Q1], "[v2,v5]" -> brA[P2, Q2],
  "[v3,anything]" -> Flatten[Table[brA[Z1, bas[[j]]], {j, 8}]],
  "[v6,anything]" -> Flatten[Table[brA[Z2, bas[[j]]], {j, 8}]]};
Print["R3  the splitting  g = span{v3,v6} + span{A,v1,v2} + span{B,v4,v5},"];
Print["    with A = -(v0 + w v7)/w  and  B = v7 :"];
Print["R3  count: departures from R^2 (+) se(2) (+) se(2) = ",
  Count[tests, r_ /; z[Last[r]] =!= Table[0, Length[Last[r]]]]];
Print["R3  count: [A, .] reaching the rotor block (0 = A commutes with v4, v5) = ",
  cnt[And[z[brA[A8, Q1]] === Table[0, 8], z[brA[A8, Q2]] === Table[0, 8]]]];

(* the degenerate case w = 0 *)
cs0 = z[csw /. w -> 0];
brA0[x_, y_] := Table[Sum[x[[i]] y[[j]] cs0[[i, j, k]], {i, 8}, {j, 8}], {k, 8}];
centre0 = Select[Range[8],
   And @@ Table[z[brA0[bas[[#]], bas[[j]]]] === Table[0, 8], {j, 8}] &];
Print["R3  at w = 0 the centre is ", (# - 1) & /@ centre0,
  "  so the algebra degenerates to R^5 (+) se(2)"];

(* ============================================================ *)
(* R4  the inductance metric in the rotating frame               *)
(* ============================================================ *)
line[]; Print["R4  THE INDUCTANCE METRIC"]; line[];
ph = {{0, 2 Pi/3, -2 Pi/3}, {-2 Pi/3, 0, 2 Pi/3}, {2 Pi/3, -2 Pi/3, 0}};
LS = Table[If[i == j, Lls + Lms, -Lms/2], {i, 3}, {j, 3}];
LR = Table[If[i == j, aa^2 Llr + Lms, -Lms/2], {i, 3}, {j, 3}];
LSR = Table[Lms Cos[th + ph[[i, j]]], {i, 3}, {j, 3}];
GG = Normal[SparseArray[{{7, 7} -> Jm}, {7, 7}]] +
   ArrayFlatten[{{LS, LSR, 0}, {Transpose[LSR], LR, 0}, {0, 0, 0}}];
sp = Rest /@ FM;   (* spatial parts of the eight extended fields *)
gab = Table[z[sp[[i + 1]] . GG . sp[[j + 1]]], {i, 7}, {j, 7}];
mus = 2/3 Lls + Lms; mur = 2/3 aa^2 Llr + Lms;
gclaim = Normal[SparseArray[{{1, 1} -> mus, {2, 2} -> mus, {3, 3} -> Lls/3,
    {4, 4} -> mur, {5, 5} -> mur, {6, 6} -> aa^2 Llr/3, {7, 7} -> Jm,
    {1, 4} -> Lms, {4, 1} -> Lms, {2, 5} -> Lms, {5, 2} -> Lms}, {7, 7}]];
Print["R4  count: departures of g(v_a,v_b) from the array (7.2) = ",
  Count[Flatten[z[gab - gclaim]], e_ /; e =!= 0]];
Print["R4  count: entries of g(v_a,v_b) still carrying theta0(t) or theta = ",
  Count[Flatten[gab], e_ /; ! FreeQ[e, th0 | th]]];
Print["    so the reduced Lagrangian (7.3) is unchanged, with no explicit time in it."];

(* ============================================================ *)
(* R5  the equations of motion, twice                            *)
(* ============================================================ *)
line[]; Print["R5  THE EQUATIONS OF MOTION"]; line[];

(* ---- route (a): the extended Hamel equation
        d/dt(dl/dxi^j) - c^k_ij xi^i dl/dxi^k - c^k_0j dl/dxi^k = f_j      ---- *)
xiv = Table[xi[a][t], {a, 7}];
lred = (1/2) xiv . gclaim . xiv;
mu = Table[D[lred, xi[a][t]], {a, 7}];
csx = csw /. {tt -> t, b00 -> 0};
hamelA = Table[
   D[mu[[j]], t] - Sum[csx[[i + 1, j + 1, k + 1]] xi[i][t] mu[[k]], {i, 7}, {k, 7}] -
    Sum[csx[[1, j + 1, k + 1]] mu[[k]], {k, 7}], {j, 7}];
Print["route (a), from the extended Hamel equation:"];
Do[Print["    j = ", j, " :  ", z[hamelA[[j]]]], {j, 7}];

(* ---- route (b): Euler-Lagrange in the abc coordinates, then contracted with v_j ---- *)
spt = sp /. {th0[tt] -> w t + 0, th -> thf[t]};
qd = Sum[xi[a][t] spt[[a + 1]], {a, 7}];
pA = (GG /. th -> thf[t]) . qd;
dLdq = Join[Table[0, 6],
   {(1/2) qd . (D[GG, th] /. th -> thf[t]) . qd}];
EL = Table[D[pA[[A]], t] - dLdq[[A]], {A, 7}] /.
   {Derivative[1][thf][t] -> xi[7][t]};
hamelB = Table[z[spt[[j + 1]] . EL], {j, 7}];
Print["route (b), from the Euler-Lagrange equations in the abc coordinates:"];
Do[Print["    j = ", j, " :  ", hamelB[[j]]], {j, 7}];
Print["R5  count: disagreements between the two routes = ",
  Count[Table[z[hamelA[[j]] - hamelB[[j]]], {j, 7}], e_ /; e =!= 0]];

(* ============================================================ *)
(* R6  against Krause's arbitrary-reference-frame model          *)
(* ============================================================ *)
line[]; Print["R6  KRAUSE'S ARBITRARY REFERENCE FRAME"]; line[];
lam = {mu[[1]], mu[[2]], mu[[4]], mu[[5]]};   (* lqs, lds, lqr, ldr *)
krause = {
  D[lam[[1]], t] + w lam[[2]],
  D[lam[[2]], t] - w lam[[1]],
  (1/3) Lls D[xi[3][t], t],
  D[lam[[3]], t] + (w - xi[7][t]) lam[[4]],
  D[lam[[4]], t] - (w - xi[7][t]) lam[[3]],
  (1/3) aa^2 Llr D[xi[6][t], t],
  Jm D[xi[7][t], t] + Lms (xi[2][t] xi[4][t] - xi[1][t] xi[5][t])};
Print["R6  count: departures of the Hamel equations from Krause's model = ",
  Count[Table[z[hamelA[[j]] - krause[[j]]], {j, 7}], e_ /; e =!= 0]];
Print["R6  count: departures at w = 0 from Theorem 7.3 of the manuscript = ",
  Count[Table[z[(hamelA[[j]] - krause[[j]]) /. w -> 0], {j, 7}], e_ /; e =!= 0]];
Print["R6  the torque equation, which must not see the frame at all: ",
  z[hamelA[[7]]]];
Print["R6  count: frame rate w surviving in the torque equation = ",
  cnt[FreeQ[z[hamelA[[7]]], w]]];

(* the invariants of Proposition 8.1 in the rotating frame *)
Print["R6  the free machine, f = 0.  Stator phasor  (lqs + I lds) e^(-I w t) :"];
sol = First[Solve[Thread[Table[hamelA[[j]], {j, 7}] == 0],
    Table[xi[a]'[t], {a, 7}]]];
drift[e_] := z[ComplexExpand[D[e, t] /. Derivative[1][thf][t] -> xi[7][t] /. sol]];
Print["R6  count: drift of the stator phasor (lqs + I lds) e^(-I w t) = ",
  cnt[drift[(lam[[1]] + I lam[[2]]) Exp[-I w t]] === 0]];
Print["R6  count: drift of the rotor phasor zeta = (lqr + I ldr) e^(I(theta - w t)) = ",
  cnt[drift[(lam[[3]] + I lam[[4]]) Exp[I (thf[t] - w t)]] === 0]];
Print["R6  count: drift of the energy = ", cnt[drift[lred] === 0]];

(* does Theorem 8.4, the pendulum, survive the change of frame? *)
Del = mus mur - Lms^2;
inv = Solve[Thread[Table[mu[[a]], {a, 7}] == Table[lm[a], {a, 7}]],
    Table[xi[a][t], {a, 7}]] // First;
torque = z[(Lms (xi[1][t] xi[5][t] - xi[2][t] xi[4][t]) /. inv)];
Print["R6  count: departures of the torque from (Lms/Del)(lqs ldr - lds lqr) = ",
  cnt[z[torque - (Lms/Del) (lm[1] lm[5] - lm[2] lm[4])] === 0]];
(* the invariants, written out:  lambda_s = As e^(I ps),  zeta = Az e^(I pz) *)
phasor = {lm[1] -> As Cos[ps + w t], lm[2] -> As Sin[ps + w t],
   lm[4] -> Az Cos[pz - thf[t] + w t], lm[5] -> Az Sin[pz - thf[t] + w t]};
tq = z[torque /. phasor];
Print["R6  the torque on the invariant level set = ", tq];
Print["R6  count: frame rate w, or any explicit t beside the rotor angle, surviving = ",
  cnt[FreeQ[tq /. thf[t] -> thsym, w | t]]];
Print["R6  count: departures from -kappa sin(theta - theta*), kappa = Lms As Az/Del = ",
  cnt[z[tq + (Lms As Az/Del) Sin[thf[t] - (pz - ps)]] === 0]];

(* ============================================================ *)
(* R7  the Euler-Poincare form and the eighth equation           *)
(* ============================================================ *)
line[]; Print["R7  EULER-POINCARE ON THE EXTENDED ALGEBRA"]; line[];
(* xihat = v0 + xi^a v_a  (the level xi^0 = 1);  muhat = (0, mu_1..mu_7) *)
xihat = Join[{1}, xiv];
muhat = Join[{0}, mu];
adstar = Table[
   Sum[xihat[[i]] csx[[i, j, k]] muhat[[k]], {i, 8}, {k, 8}], {j, 8}];
Print["R7  count: departures of the Hamel equations from  d(mu)/dt - ad*_xihat mu = f  = ",
  Count[Table[z[hamelA[[j]] - (D[muhat[[j + 1]], t] - adstar[[j + 1]])], {j, 7}],
   e_ /; e =!= 0]];
Print["R7  the eighth (j = 0) equation reads  0 = ", z[adstar[[1]]]];
Print["R7  count: obstruction to the level xi^0 = 1 being preserved = ",
  cnt[z[adstar[[1]]] === 0]];
line[];
Print["done."];
