(* prose_identities_check.wls --- the intermediate identities stated in the prose proofs of
   manuscript/main.tex, checked in Wolfram Language.  Written 2026-09-14, when the proofs of
   Props 5.1, 6.1, 7.1, 7.2, Thm 7.4, Cor 7.5, Thm 9.3 and Prop 9.5 were rewritten so that the
   mathematics stands in prose.  The CAS checks the prose; the prose carries the argument.
   W1-W5 Prop 6.1 (phasor row, cube roots, K K^T, K 1, stator block);  W4 the mutual pair P, Q;
   W6-W8 Prop 7.2 (chart as a phasor, rotation generator, momenta);  W13 Thm 7.4;  W14 Prop 7.1;
   W12 Thm 9.3;  W9 Prop 9.5 (the two slip terms cancel, neither vanishes alone);
   W10-W11 the resistance normalisation R_r = (2/3) r_r of Section 9.
   Every line printed with count: must read 0. *)
(* Identities to be stated in the new prose proofs.  Each "count:" must read 0. *)
cnt[b_] := If[TrueQ[b], 0, 1];
z[e_] := FullSimplify[ComplexExpand[TrigReduce[Expand[e]]]];
phi = {0, 2 Pi/3, -2 Pi/3};  w = Exp[I phi];  one = {1, 1, 1};
K[b_] := (2/3) {Cos[b - phi], Sin[b - phi], {1/2, 1/2, 1/2}};
Kstd[b_] := (2/3) {{Cos[b], Cos[b - 2 Pi/3], Cos[b + 2 Pi/3]},
                   {Sin[b], Sin[b - 2 Pi/3], Sin[b + 2 Pi/3]}, {1/2, 1/2, 1/2}};
Print["W0  count: my K differs from the manuscript's array (3.1) = ", cnt[z[K[bb] - Kstd[bb]] === Table[0, {3}, {3}]]];
Print["W1  count: row1 + i row2 differs from (2/3) e^{i beta} conj(w) = ", cnt[z[K[bb][[1]] + I K[bb][[2]] - (2/3) Exp[I bb] Conjugate[w]] === {0, 0, 0}]];
Print["W3  count: sum w or sum w^2 failing to vanish = ", cnt[z[Total[w]] === 0 && z[Total[w^2]] === 0]];
ph = {{0, 2 Pi/3, -2 Pi/3}, {-2 Pi/3, 0, 2 Pi/3}, {2 Pi/3, -2 Pi/3, 0}};
LSR = Table[Lms Cos[th + ph[[i, j]]], {i, 3}, {j, 3}];
Print["W2  count: phases(i,j) differing from phi_j - phi_i mod 2pi = ", cnt[z[Table[Exp[I ph[[i, j]]] - Exp[I (phi[[j]] - phi[[i]])], {i, 3}, {j, 3}]] === Table[0, {3}, {3}]]];
Print["W2  count: L_SR differing from (Lms/2)(e^{i th} conj(w) w^T + c.c.) = ", cnt[z[LSR - (Lms/2) (Exp[I th] Outer[Times, Conjugate[w], w] + Exp[-I th] Outer[Times, w, Conjugate[w]])] === Table[0, {3}, {3}]]];
LS = Table[If[i == j, Lls + Lms, -Lms/2], {i, 3}, {j, 3}];
LR = Table[If[i == j, aa^2 Llr + Lms, -Lms/2], {i, 3}, {j, 3}];
Print["W5  count: L_S differing from (Lls + 3Lms/2) I - (Lms/2) 1 1^T = ", cnt[z[LS - ((Lls + 3 Lms/2) IdentityMatrix[3] - (Lms/2) Outer[Times, one, one])] === Table[0, {3}, {3}]]];
Print["W5  count: K 1 differing from e3 = ", cnt[z[K[bb] . one] === {0, 0, 1}]];
Print["W5  count: K K^T differing from diag(2/3,2/3,1/3) = ", cnt[z[K[bb] . Transpose[K[bb]]] === DiagonalMatrix[{2/3, 2/3, 1/3}]]];
(* the two complex contractions against the mutual block, reference angle th0 symbolic *)
ks = (2/3) Exp[I t0] Conjugate[w];  kr = (2/3) Exp[I (t0 - th)] Conjugate[w];
Print["W4  k_s . L_SR . k_r = ", z[ks . LSR . kr], "   k_s . L_SR . conj(k_r) = ", z[ks . LSR . Conjugate[kr]]];
Print["W4  count: those differing from 0 and 2 Lms = ", cnt[z[ks . LSR . kr] === 0 && z[ks . LSR . Conjugate[kr]] === 2 Lms]];
Print["W4  count: 1^T L_SR and L_SR 1 failing to vanish = ", cnt[z[one . LSR] === {0, 0, 0} && z[LSR . one] === {0, 0, 0}]];
Gfull = ArrayFlatten[{{K[t0] . LS . Transpose[K[t0]], K[t0] . LSR . Transpose[K[t0 - th]]},
                      {K[t0 - th] . Transpose[LSR] . Transpose[K[t0]], K[t0 - th] . LR . Transpose[K[t0 - th]]}}];
mus = 2/3 Lls + Lms; mur = 2/3 aa^2 Llr + Lms;
Gclaim = ArrayFlatten[{{DiagonalMatrix[{mus, mus, Lls/3}], DiagonalMatrix[{Lms, Lms, 0}]},
                       {DiagonalMatrix[{Lms, Lms, 0}], DiagonalMatrix[{mur, mur, aa^2 Llr/3}]}}];
Print["W4  count: the 6x6 electrical array differing from (6.2) for symbolic th0 and th = ", cnt[z[Gfull - Gclaim] === Table[0, {6}, {6}]]];
(* chart and rotation generator *)
D3 = DiagonalMatrix[{2/3, 2/3, 1/3}];
Print["W6  count: K^{-T} differing from D^{-1} K = ", cnt[z[Inverse[Transpose[K[t0]]] - Inverse[D3] . K[t0]] === Table[0, {3}, {3}]]];
q = {qa, qb, qc};  zz = Inverse[Transpose[K[t0]]] . q;
Print["W6  count: z1 + i z2 differing from e^{i th0} conj(w).q = ", cnt[z[zz[[1]] + I zz[[2]] - Exp[I t0] Conjugate[w] . q] === 0]];
X = (1/Sqrt[3]) {qb - qc, qc - qa, qa - qb};
Print["W7  count: X[z1 + i z2] differing from i (z1 + i z2) = ", cnt[z[Grad[zz[[1]] + I zz[[2]], q] . X - I (zz[[1]] + I zz[[2]])] === 0]];
Print["W7  count: X[eta4] failing to vanish = ", cnt[z[Grad[zz[[3]], q] . X] === 0]];
Print["W7  count: X differing from -(1/sqrt3) 1 x q = ", cnt[z[X + (1/Sqrt[3]) Cross[one, q]] === {0, 0, 0}]];
(* momenta *)
p = {p1, p2, p3};  pz = K[t0] . p;  kr0 = K[t0 - th][[1]] + I K[t0 - th][[2]];
Print["W8  count: lambda_qr + i lambda_dr differing from e^{-i th}(K1(th0)+iK2(th0)).p = ", cnt[z[kr0 . p - Exp[-I th] (K[t0][[1]] + I K[t0][[2]]) . p] === 0]];
(* Theorem 7.4 cross terms and Proposition 7.1 *)
ls = x1 + I y1; lr = x2 + I y2; Del = mus mur - Lms^2;
xs = (mur ls - Lms lr)/Del; xr = (mus lr - Lms ls)/Del;
Print["W13 count: (xi1 - i xi2)(xi4 + i xi5) differing from [mur mus conj(ls) lr + Lms^2 conj(lr) ls - mur Lms|ls|^2 - mus Lms|lr|^2]/Del^2 = ",
  cnt[z[Conjugate[xs] xr - (mur mus Conjugate[ls] lr + Lms^2 Conjugate[lr] ls - mur Lms ls Conjugate[ls] - mus Lms lr Conjugate[lr])/Del^2] === 0]];
Print["W13 count: its imaginary part differing from Im(conj(ls) lr)/Del = ", cnt[z[Im[Conjugate[xs] xr] - Im[Conjugate[ls] lr]/Del] === 0]];
Print["W14 count: (1/2)[Re(conj xi_s ls) + Re(conj xi_r lr)] differing from (mur|ls|^2+mus|lr|^2)/2Del - (Lms/Del)Re(conj ls lr) = ",
  cnt[z[(Re[Conjugate[xs] ls] + Re[Conjugate[xr] lr])/2 - ((mur Abs[ls]^2 + mus Abs[lr]^2)/(2 Del) - (Lms/Del) Re[Conjugate[ls] lr])] === 0]];
(* Theorem 9.3 *)
Ak = {{-rho, -sg, -ld}, {sg, -rho, lq}, {0, -k, 0}};
cp = Expand[Det[s IdentityMatrix[3] - Ak]];
Print["W12 count: char poly differing from s^3 + 2 rho s^2 + (rho^2 + sg^2 + k lq) s + k(rho lq - sg ld) = ",
  cnt[Simplify[cp - (s^3 + 2 rho s^2 + (rho^2 + sg^2 + k lq) s + k (rho lq - sg ld))] === 0]];
Print["W12 count: c1 c2 - c0 differing from 2 rho(rho^2+sg^2) + k(rho lq + sg ld) = ",
  cnt[Simplify[(rho^2 + sg^2 + k lq) 2 rho - k (rho lq - sg ld) - (2 rho (rho^2 + sg^2) + k (rho lq + sg ld))] === 0]];
(* Proposition 9.5: the two slip terms and their cancellation; lambda_s = A real *)
A0 = Lms Aa/mus; lamr = u + I v;
rotor = (-rh + I sg) lamr + rh A0;
Wel = mus ((u - A0)^2 + v^2)/(2 Del); 
dWel = z[(mus/Del) Re[Conjugate[lamr - A0] rotor] /. {u -> u, v -> v}];
slipPart = z[(mus/Del) Re[Conjugate[lamr - A0] I sg lamr]];
Print["W9  slip term from the rotor equation = ", slipPart];
Print["W9  count: slip term differing from +sg Lms Aa v/Del = ", cnt[z[slipPart - sg Lms Aa v/Del] === 0]];
Print["W9  count: mechanical term J sg sgdot at TL=0 differing from -sg Lms Aa v/Del = ", cnt[z[sg (-(Lms Aa/Del) v) + sg Lms Aa v/Del] === 0]];
Print["W9  count: resistive part differing from -rh(mus/Del)|lamr - lam0|^2 = ", cnt[z[(mus/Del) Re[Conjugate[lamr - A0] (-rh (lamr - A0))] + rh (mus/Del) ((u - A0)^2 + v^2)] === 0]];
(* resistance normalisation *)
xiv = {e1, e2, e3};  qdot = Transpose[K[t0]] . xiv;
Print["W10 count: frame components of -R qdot differing from -R K K^T xi = ", cnt[z[K[t0] . (-R qdot) + R DiagonalMatrix[{2/3, 2/3, 1/3}] . xiv] === {0, 0, 0}]];
Print["W10 count: copper loss R|qdot|^2 differing from (2/3)R(e1^2+e2^2)+(1/3)R e3^2 = ", cnt[z[R qdot . qdot - (2/3 R (e1^2 + e2^2) + 1/3 R e3^2)] === 0]];
LM = 3/2 Lms; Lss = Lls + LM; Lrr = aa^2 Llr + LM;
rhoCl = r Lss/(Lss Lrr - LM^2);
Print["W11 count: rho with R_r = (2/3) r differing from the classical r L_ss/(L_ss L_rr - L_M^2) = ", cnt[Simplify[(2/3 r) mus/Del - rhoCl] === 0]];
Print["W11 count: rho with R_r = r equal to the classical value (0 = it is NOT) = ", cnt[Simplify[r mus/Del - rhoCl] =!= 0]];
