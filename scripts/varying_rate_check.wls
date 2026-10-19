#!/usr/bin/env wolframscript
(* ::Package:: *)

(* Problem 10.1 of manuscript/main.tex --- a frame of varying rate.
   Wolfram Language.  Written 2026-09-14.  Companion to rotating_frame_check.wls.

   Theorem 8.1 says the extended qd0 frame spans a Lie algebra only when theta0'' = 0.
   Under a variable frequency drive the supply frequency itself varies.  What replaces
   the Euler-Poincare reduction?  The answer turns on a single object.

     V1  the qd0 frame of one reference angle is carried to that of another by the map
         Psi(beta) rotating (v1,v2) and (v4,v5) through beta.  Is Psi an AUTOMORPHISM
         of g = R^4 (+) se(2)?
     V2  its generator D is a derivation of g; is it inner or outer?
     V3  the extended bracket is [v0, X] = theta0'(t) D(X) for every X in g;
     V4  hence the span closes iff theta0' is constant, and is then R (x)_{w D} g;
     V5  the equations of motion for ARBITRARY theta0(t), derived twice and compared;
     V6  their form:  mu-dot = ad*_xi mu + theta0'(t) D* mu + f, Euler-Poincare on the
         FIXED algebra g driven by a prescribed curve in Der(g);
     V7  the conserved linkages, the energy and the pendulum, for arbitrary theta0(t);
     V8  the two descriptions are conjugate:  mu_rot(t) = Psi(theta0(t)) mu_stat(t).

   Conventions as in rotating_frame_check.wls, from which the frame is taken.
   Every line printed with "count:" must read 0.
*)

Off[Solve::ifun]; Off[Solve::svars];
line[] := Print[StringRepeat["-", 78]];
z[e_] := FullSimplify[TrigReduce[Expand[e]]];
cnt[b_] := If[TrueQ[b], 0, 1];
zeroQ[v_] := z[v] === Table[0, Length[v]];

(* ============================================================ *)
(* the algebra g of Theorem 5.1, in the basis v1..v7            *)
(* ============================================================ *)
cg = Table[0, {7}, {7}, {7}];
cg[[4, 7, 5]] = -1; cg[[7, 4, 5]] = 1;    (* [v4,v7] = -v5 *)
cg[[5, 7, 4]] = 1;  cg[[7, 5, 4]] = -1;   (* [v5,v7] =  v4 *)
br[x_, y_] := Table[Sum[x[[i]] y[[j]] cg[[i, j, k]], {i, 7}, {j, 7}], {k, 7}];
e = IdentityMatrix[7];

(* ============================================================ *)
(* V1  Psi(beta) and the automorphism test                       *)
(* ============================================================ *)
line[]; Print["V1  IS THE CHANGE OF REFERENCE ANGLE AN AUTOMORPHISM OF g ?"]; line[];
Psi[b_] := Module[{m = IdentityMatrix[7]},
   m[[1, 1]] = Cos[b]; m[[1, 2]] = -Sin[b];
   m[[2, 1]] = Sin[b]; m[[2, 2]] = Cos[b];
   m[[4, 4]] = Cos[b]; m[[4, 5]] = -Sin[b];
   m[[5, 4]] = Sin[b]; m[[5, 5]] = Cos[b]; m];
ap[b_, x_] := Psi[b] // Transpose // (# . x &);   (* Psi(v_i) = sum_k M[[i,k]] v_k *)
apply[b_, x_] := Transpose[Psi[b]] . x;
autofail = Select[Flatten[Table[{i, j}, {i, 7}, {j, 7}], 1],
   ! zeroQ[apply[bb, br[e[[#[[1]]]], e[[#[[2]]]]]] -
        br[apply[bb, e[[#[[1]]]]], apply[bb, e[[#[[2]]]]]]] &];
Print["V1  count: bracket pairs on which Psi(beta) fails to be an automorphism = ",
  Length[autofail]];
Print["V1  count: departures of Psi from a one-parameter group, Psi(b)Psi(c) = Psi(b+c) = ",
  cnt[z[Psi[bb] . Psi[cc] - Psi[bb + cc]] === Table[0, {7}, {7}]]];
Print["V1  count: departures of Psi from orthogonality = ",
  cnt[z[Transpose[Psi[bb]] . Psi[bb] - IdentityMatrix[7]] === Table[0, {7}, {7}]]];

(* ============================================================ *)
(* V2  the generator D, and whether it is inner                  *)
(* ============================================================ *)
line[]; Print["V2  THE GENERATOR D"]; line[];
DD = D[Psi[b], b] /. b -> 0;
Print["V2  D sends v1 -> ", Transpose[DD] . e[[1]], " and v4 -> ", Transpose[DD] . e[[4]]];
dact[x_] := Transpose[DD] . x;
derfail = Select[Flatten[Table[{i, j}, {i, 7}, {j, 7}], 1],
   ! zeroQ[dact[br[e[[#[[1]]]], e[[#[[2]]]]]] -
        br[dact[e[[#[[1]]]]], e[[#[[2]]]]] - br[e[[#[[1]]]], dact[e[[#[[2]]]]]]] &];
Print["V2  count: Leibniz failures of D (0 confirms D is a derivation of g) = ",
  Length[derfail]];
(* inner?  solve ad_X = D *)
xs = Array[xx, 7];
adX = Table[br[xs, e[[j]]], {j, 7}];
Dmat = Table[dact[e[[j]]], {j, 7}];
innersol = Solve[Thread[Flatten[adX] == Flatten[Dmat]], xs];
Print["V2  solutions X of ad_X = D : ", innersol];
Print["V2  count: inner solutions (0 confirms D is an OUTER derivation) = ",
  Length[innersol]];
Print["V2  why: v1 and v2 are central in g, so ad_X(v1) = 0 for every X, while D(v1) = -v2."];
Print["V2  count: departures of ad_X(v1) from 0 for a general X = ",
  cnt[zeroQ[br[xs, e[[1]]]]]];
(* on the se(2) block D agrees with -ad_{v7} *)
Print["V2  count: departures of D from antisymmetry, D* = -D (needed for Thm 8.7) = ",
  cnt[z[DD + Transpose[DD]] === Table[0, {7}, {7}]]];
Print["V2  count: departures of D from -ad_{v7} on span{v4,v5,v7} = ",
  Count[Table[z[dact[e[[k]]] + br[e[[7]], e[[k]]]], {k, {4, 5, 7}}],
   q_ /; q =!= Table[0, {7}]]];

(* ============================================================ *)
(* V3  the extended bracket is theta0'(t) D                      *)
(* ============================================================ *)
line[]; Print["V3  THE EXTENDED BRACKET"]; line[];
ext = {tt, qsa, qsb, qsc, qra, qrb, qrc, th};
KK[b_] := (2/3) {{Cos[b], Cos[b - 2 Pi/3], Cos[b + 2 Pi/3]},
                 {Sin[b], Sin[b - 2 Pi/3], Sin[b + 2 Pi/3]},
                 {1/2, 1/2, 1/2}};
b0 = th0[tt];
FM = Join[{UnitVector[8, 1]},
   Table[Join[{0}, KK[b0][[i]], {0, 0, 0}, {0}], {i, 3}],
   Table[Join[{0}, {0, 0, 0}, KK[b0 - th][[i]], {0}], {i, 3}],
   {UnitVector[8, 8]}];
vbrk[X_, Y_] := Table[Sum[X[[b]] D[Y[[a]], ext[[b]]] - Y[[b]] D[X[[a]], ext[[b]]],
    {b, 8}], {a, 8}];
inFrame[X_] := z /@ LinearSolve[Transpose[FM], X];
(* [v0, v_a] in the frame, dropping the v0 slot, against theta0' D(v_a) *)
lhs = Table[Rest[inFrame[vbrk[FM[[1]], FM[[a + 1]]]]], {a, 7}];
rhs = Table[Derivative[1][th0][tt] dact[e[[a]]], {a, 7}];
Print["V3  count: departures of [v0, v_a] from theta0'(t) D(v_a), a = 1..7 = ",
  Count[Table[z[lhs[[a]] - rhs[[a]]], {a, 7}], q_ /; q =!= Table[0, {7}]]];
Print["V3  this holds for an ARBITRARY smooth theta0(t); no constancy is used."];

(* ============================================================ *)
(* V4  closure                                                   *)
(* ============================================================ *)
line[]; Print["V4  CLOSURE"]; line[];
Print["V4  the structure functions carrying the index 0 are the entries of theta0'(t) D,"];
Print["    so the span is a Lie algebra iff theta0' is constant, and is then the"];
Print["    semidirect product  R (x)_{w D} g,  w = theta0'."];
Print["V4  count: departures of the w-uniform bracket from the semidirect product = ",
  Count[Table[z[(lhs[[a]] /. Derivative[1][th0][tt] -> w) - w dact[e[[a]]]], {a, 7}],
   q_ /; q =!= Table[0, {7}]]];
(* consistency with Theorem 8.1: R (x)_{wD} g  ==  R^2 (+) se(2) (+) se(2) *)
AA = -(1/w) (UnitVector[8, 1] + w UnitVector[8, 8]);
cext = Table[0, {8}, {8}, {8}];
Do[cext[[i + 1, j + 1, k + 1]] = cg[[i, j, k]], {i, 7}, {j, 7}, {k, 7}];
Do[cext[[1, a + 1, k + 1]] = w dact[e[[a]]][[k]];
   cext[[a + 1, 1, k + 1]] = -w dact[e[[a]]][[k]], {a, 7}, {k, 7}];
brE[x_, y_] := Table[Sum[x[[i]] y[[j]] cext[[i, j, k]], {i, 8}, {j, 8}], {k, 8}];
E8 = IdentityMatrix[8];
(* E8[[k]] is v_{k-1}, so v1..v7 occupy slots 2..8 *)
se2tests = Join[
  {brE[AA, E8[[2]]] - E8[[3]], brE[AA, E8[[3]]] + E8[[2]],
   brE[AA, E8[[5]]], brE[AA, E8[[6]]], brE[AA, E8[[8]]],
   brE[E8[[8]], E8[[5]]] - E8[[6]], brE[E8[[8]], E8[[6]]] + E8[[5]],
   brE[E8[[2]], E8[[3]]], brE[E8[[5]], E8[[6]]]},
  Flatten[Table[{brE[E8[[4]], E8[[j]]], brE[E8[[7]], E8[[j]]]}, {j, 8}], 1]];
Print["V4  count: departures of R (x)_{wD} g from R^2 (+) se(2) (+) se(2), A = -(v0+w v7)/w = ",
  Count[se2tests, q_ /; z[q] =!= Table[0, {8}]]];

(* ============================================================ *)
(* V5  the equations of motion for arbitrary theta0(t)           *)
(* ============================================================ *)
line[]; Print["V5  THE EQUATIONS OF MOTION, theta0(t) ARBITRARY"]; line[];
ph = {{0, 2 Pi/3, -2 Pi/3}, {-2 Pi/3, 0, 2 Pi/3}, {2 Pi/3, -2 Pi/3, 0}};
LS = Table[If[i == j, Lls + Lms, -Lms/2], {i, 3}, {j, 3}];
LR = Table[If[i == j, aa^2 Llr + Lms, -Lms/2], {i, 3}, {j, 3}];
LSR = Table[Lms Cos[th + ph[[i, j]]], {i, 3}, {j, 3}];
GG = Normal[SparseArray[{{7, 7} -> Jm}, {7, 7}]] +
   ArrayFlatten[{{LS, LSR, 0}, {Transpose[LSR], LR, 0}, {0, 0, 0}}];
mus = 2/3 Lls + Lms; mur = 2/3 aa^2 Llr + Lms;
gcl = Normal[SparseArray[{{1, 1} -> mus, {2, 2} -> mus, {3, 3} -> Lls/3,
    {4, 4} -> mur, {5, 5} -> mur, {6, 6} -> aa^2 Llr/3, {7, 7} -> Jm,
    {1, 4} -> Lms, {4, 1} -> Lms, {2, 5} -> Lms, {5, 2} -> Lms}, {7, 7}]];
sp = Rest /@ FM;
Print["V5  count: departures of g(v_a,v_b) from the array (6.2), theta0(t) arbitrary = ",
  Count[Flatten[z[Table[sp[[i + 1]] . GG . sp[[j + 1]], {i, 7}, {j, 7}] - gcl]],
   q_ /; q =!= 0]];

xiv = Table[xi[a][t], {a, 7}];
lred = (1/2) xiv . gcl . xiv;
mu = Table[D[lred, xi[a][t]], {a, 7}];
wt = Derivative[1][th0f][t];
(* route (a): extended Hamel with c^k_{0j} = theta0'(t) D *)
hamelA = Table[
   D[mu[[j]], t] - Sum[cg[[i, j, k]] xi[i][t] mu[[k]], {i, 7}, {k, 7}] -
    wt Sum[dact[e[[j]]][[k]] mu[[k]], {k, 7}], {j, 7}];
(* route (b): Euler-Lagrange in the abc coordinates *)
spt = sp /. {th0[tt] -> th0f[t], th -> thf[t]};
qd = Sum[xi[a][t] spt[[a + 1]], {a, 7}];
pA = (GG /. th -> thf[t]) . qd;
dLdq = Join[Table[0, 6], {(1/2) qd . (D[GG, th] /. th -> thf[t]) . qd}];
EL = Table[D[pA[[A]], t] - dLdq[[A]], {A, 7}] /. Derivative[1][thf][t] -> xi[7][t];
hamelB = Table[z[spt[[j + 1]] . EL], {j, 7}];
Print["V5  count: disagreements between the extended Hamel and Euler-Lagrange routes = ",
  Count[Table[z[hamelA[[j]] - hamelB[[j]]], {j, 7}], q_ /; q =!= 0]];
lam = {mu[[1]], mu[[2]], mu[[4]], mu[[5]]};
krause = {D[lam[[1]], t] + wt lam[[2]], D[lam[[2]], t] - wt lam[[1]],
   (1/3) Lls D[xi[3][t], t],
   D[lam[[3]], t] + (wt - xi[7][t]) lam[[4]], D[lam[[4]], t] - (wt - xi[7][t]) lam[[3]],
   (1/3) aa^2 Llr D[xi[6][t], t],
   Jm D[xi[7][t], t] + Lms (xi[2][t] xi[4][t] - xi[1][t] xi[5][t])};
Print["V5  count: departures from Krause's model with w replaced by theta0'(t) = ",
  Count[Table[z[hamelA[[j]] - krause[[j]]], {j, 7}], q_ /; q =!= 0]];
Print["V5  count: theta0'' appearing anywhere in the equations of motion = ",
  cnt[FreeQ[z[hamelA], Derivative[2][th0f]]]];

(* ============================================================ *)
(* V6  the driven Euler-Poincare form                            *)
(* ============================================================ *)
line[]; Print["V6  EULER-POINCARE DRIVEN BY A CURVE IN Der(g)"]; line[];
adstar = Table[Sum[xi[i][t] cg[[i, j, k]] mu[[k]], {i, 7}, {k, 7}], {j, 7}];
Dstar = Table[Sum[dact[e[[j]]][[k]] mu[[k]], {k, 7}], {j, 7}];
Print["V6  count: departures from  d(mu)/dt = ad*_xi mu + theta0'(t) D* mu + f = ",
  Count[Table[z[hamelA[[j]] - (D[mu[[j]], t] - adstar[[j]] - wt Dstar[[j]])], {j, 7}],
   q_ /; q =!= 0]];

(* ============================================================ *)
(* V7  the integrals, for arbitrary theta0(t)                    *)
(* ============================================================ *)
line[]; Print["V7  THE INTEGRALS"]; line[];
sol = First[Solve[Thread[Table[hamelA[[j]], {j, 7}] == 0], Table[xi[a]'[t], {a, 7}]]];
drift[ex_] := z[ComplexExpand[D[ex, t] /. Derivative[1][thf][t] -> xi[7][t] /. sol]];
Print["V7  count: drift of the stator phasor lambda_s e^(-I theta0(t)) = ",
  cnt[drift[(lam[[1]] + I lam[[2]]) Exp[-I th0f[t]]] === 0]];
Print["V7  count: drift of the rotor phasor lambda_r e^(I(theta - theta0(t))) = ",
  cnt[drift[(lam[[3]] + I lam[[4]]) Exp[I (thf[t] - th0f[t])]] === 0]];
Print["V7  count: drift of the energy = ", cnt[drift[lred] === 0]];
Del = mus mur - Lms^2;
inv = First[Solve[Thread[Table[mu[[a]], {a, 7}] == Table[lm[a], {a, 7}]],
    Table[xi[a][t], {a, 7}]]];
torque = z[Lms (xi[1][t] xi[5][t] - xi[2][t] xi[4][t]) /. inv];
phasor = {lm[1] -> As Cos[ps + th0f[t]], lm[2] -> As Sin[ps + th0f[t]],
   lm[4] -> Az Cos[pz - thf[t] + th0f[t]], lm[5] -> Az Sin[pz - thf[t] + th0f[t]]};
tq = z[torque /. phasor];
Print["V7  the torque on the invariant level set = ", tq];
Print["V7  count: theta0 surviving in it = ",
  cnt[FreeQ[tq /. thf[t] -> thsym, th0f | t]]];
Print["V7  count: departures from -kappa sin(theta - theta*), kappa = Lms As Az/Del = ",
  cnt[z[tq + (Lms As Az/Del) Sin[thf[t] - (pz - ps)]] === 0]];

(* ============================================================ *)
(* V8  the two descriptions are conjugate                        *)
(* ============================================================ *)
line[]; Print["V8  CONJUGACY OF THE TWO DESCRIPTIONS"]; line[];
Print["V8  count: departures of Psi from preserving the inductance array, Psi I Psi^T = I = ",
  cnt[z[Psi[bb] . gcl . Transpose[Psi[bb]] - gcl] === Table[0, {7}, {7}]]];
(* the map between the two sets of quasi-velocities, read off the two frames *)
spStat = Rest /@ (FM /. th0[tt] -> 0) // Rest;
spRot = Rest /@ (FM /. th0[tt] -> th0f[t]) // Rest;
TT = z /@ (Inverse[Transpose[spRot]] . Transpose[spStat]);
Print["V8  count: departures of the frame-to-frame map from Psi(theta0(t)) = ",
  cnt[z[TT - Psi[th0f[t]]] === Table[0, {7}, {7}]]];
must = Table[ms[a][t], {a, 7}];
xistat = Inverse[gcl] . must;
epstat = Table[D[must[[j]], t] -
    Sum[cg[[i, j, k]] xistat[[i]] must[[k]], {i, 7}, {k, 7}], {j, 7}];
solstat = First[Solve[Thread[epstat == 0], Table[ms[a]'[t], {a, 7}]]];
murot = z /@ (gcl . TT . xistat);
Print["V8  count: departures of mu_rot from Psi(theta0(t)) mu_stat = ",
  cnt[z[murot - Psi[th0f[t]] . must] === Table[0, 7]]];
xirot = Inverse[gcl] . murot;
driven = Table[
   z[(D[murot[[j]], t] - Sum[cg[[i, j, k]] xirot[[i]] murot[[k]], {i, 7}, {k, 7}]
      - wt Sum[dact[e[[j]]][[k]] murot[[k]], {k, 7}]) /. solstat], {j, 7}];
Print["V8  count: failures of mu_rot to solve the driven equation when mu_stat solves ",
  "the autonomous one = ", Count[driven, q_ /; q =!= 0]];
line[]; Print["done."];
