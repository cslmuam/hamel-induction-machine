# Theorem 5.1 and Proposition 5.2 of manuscript/main.tex --- Maple verification.
# theta0 is kept symbolic throughout.  Every "count" line must print 0 and every
# comparison list must print zeros.  Written 2026-09-14.
restart:
with(DifferentialGeometry): with(LieAlgebras): with(Tools): with(LinearAlgebra):
interface(warnlevel = 0):
DGsetup([qsa,qsb,qsc,qra,qrb,qrc,th], Q):
DX := DGinfo("FrameBaseVectors"): dQ := DGinfo("FrameBaseForms"):
K := b -> 2/3*Matrix([[cos(b), cos(b-2*Pi/3), cos(b+2*Pi/3)],
                      [sin(b), sin(b-2*Pi/3), sin(b+2*Pi/3)],
                      [1/2, 1/2, 1/2]]):
Ks := K(th0): Kr := K(th0-th):
for i to 3 do
  v[i]   := evalDG(add(Ks[i,j]*DX[j],   j=1..3)):
  v[i+3] := evalDG(add(Kr[i,j]*DX[j+3], j=1..3)):
od:
v[7] := DX[7]:
V := [seq(v[i], i=1..7)]:
zc := proc(d, frm) local m;
  if d = 0 then [0$7] else [seq(simplify(Hook(d, frm[m])), m=1..7)] fi
end proc:
Z := e -> simplify(convert(expand(e), exp)):

# ---------------- Theorem 5.1 ----------------
printf("A1  det K(beta) = %a\n", simplify(Determinant(K(beta)))):
M := Matrix([seq(zc(v[i], dQ), i=1..7)]):
printf("A1  det of the 7x7 frame matrix = %a\n", simplify(Determinant(M))):
for i to 6 do for j from i+1 to 7 do
  cl := zc(LieBracket(v[i], v[j]), dQ):
  if cl <> [0$7] then
    c := LinearSolve(Transpose(M), Vector(cl)):
    printf("A2  [v%d,v%d] = frame components %a\n", i, j, map(simplify, convert(c, list))):
  fi:
od: od:
cnt := 0:
for i to 5 do for j from i+1 to 6 do for k from j+1 to 7 do
  J3 := evalDG(LieBracket(v[i], LieBracket(v[j], v[k]))
             + LieBracket(v[j], LieBracket(v[k], v[i]))
             + LieBracket(v[k], LieBracket(v[i], v[j]))):
  if zc(J3, dQ) <> [0$7] then cnt := cnt + 1 fi:
od: od: od:
printf("A3  count: Jacobi failures on the 35 triples of vector fields = %d\n", cnt):
LD := LieAlgebraData(V, g7):
DGsetup(LD):
E := DGinfo("FrameBaseVectors"):
printf("A4  Query Jacobi = %a\n", Query("Jacobi")):
printf("A4  centre = %a\n", map(e -> DGinfo(e, "CoefficientList", "all"), Center())):
printf("A4  span{e1,e2,e3,e6} ideal = %a ; span{e4,e5,e7} ideal = %a\n",
       Query([E[1],E[2],E[3],E[6]], "Ideal"), Query([E[4],E[5],E[7]], "Ideal")):
DGsetup([a1,a2,a3,a4,x,y,phi], G):
DG := DGinfo("FrameBaseVectors"): dG := DGinfo("FrameBaseForms"):
W := [DG[1], DG[2], DG[3],
      evalDG( cos(phi)*DG[5] + sin(phi)*DG[6]),
      evalDG(-sin(phi)*DG[5] + cos(phi)*DG[6]),
      DG[4], DG[7]]:
LD2 := LieAlgebraData(W, h7):
printf("A5  structure constants g = %a ; R^4+se(2) = %a ; identical = %a\n",
       op(2, op(1, LD)), op(2, op(1, LD2)), evalb(op(2, op(1, LD)) = op(2, op(1, LD2)))):

# ---------------- Proposition 5.2 ----------------
ChangeFrame(Q):
Ai := MatrixInverse(Transpose(Ks)): Bi := MatrixInverse(Transpose(K(th0))):
Av := Ai . Vector([qsa,qsb,qsc]): Bv := Bi . Vector([qra,qrb,qrc]):
Phi := Transformation(Q, G, [a1 = Av[1], a2 = Av[2], a3 = Av[3], a4 = Bv[3],
                             x = Bv[1], y = Bv[2], phi = th]):
printf("B2  Jacobian determinant of Phi = %a\n", simplify(Determinant(DGinfo(Phi, "JacobianMatrix")))):
Phiinv := InverseTransformation(Phi):
cnt := 0:
for i to 7 do
  d := map(e -> simplify(subs(th = phi, e)), zc(evalDG(Pushforward(Phi, v[i]) - W[i]), dG)):
  if d <> [0$7] then cnt := cnt + 1: printf("B3  mismatch for v%d: %a\n", i, d) fi:
od:
printf("B3  count: qd0 fields whose pushforward differs from the R^4 x SE(2) frame = %d\n", cnt):
ChangeFrame(G):
R := [DG[1], DG[2], DG[3], DG[5], DG[6], DG[4], evalDG(DG[7] - y*DG[5] + x*DG[6])]:
cnt := 0:
for k to 7 do for j to 7 do
  if zc(LieBracket(R[k], W[j]), dG) <> [0$7] then cnt := cnt + 1 fi:
od: od:
printf("B4  count: non-vanishing [R_k, W_j] among 49 pairs = %d\n", cnt):
LT := Transformation(G, G, [a1=a1+b1, a2=a2+b2, a3=a3+b3, a4=a4+b4,
                            x = xh + cos(ph)*x - sin(ph)*y,
                            y = yh + sin(ph)*x + cos(ph)*y, phi = phi + ph]):
cnt := 0:
for j to 7 do
  P := zc(Pushforward(LT, W[j]), dG):
  Wimg := map(e -> subs(phi = phi + ph, e), zc(W[j], dG)):
  if map(simplify, P - Wimg) <> [0$7] then cnt := cnt + 1 fi:
od:
printf("B4  count: fields W not preserved by a general left translation = %d\n", cnt):

# ---------------- consistency: invariance of the inductance metric ----------------
ChangeFrame(Q):
phases := Array(antisymmetric, 1..3, 1..3):
phases[1,2] := 2*Pi/3: phases[1,3] := -2*Pi/3: phases[2,3] := 2*Pi/3:
LS  := Matrix(3,3,(i,j) -> `if`(i=j, Lls+Lms, -Lms/2)):
LRr := Matrix(3,3,(i,j) -> `if`(i=j, Llr*a^2+Lms, -Lms/2)):
LSR := Matrix(3,3,(i,j) -> `if`(i=j, Lms*cos(th), Lms*cos(th + phases[i,j]))):
Lp := <<LS, Transpose(LSR)> | <LSR, LRr>>:
gm := evalDG(add(add(Lp[i,j]*(dQ[i] &t dQ[j]), j=1..6), i=1..6) + J*(dQ[7] &t dQ[7])):
Cexp := Matrix(7,7,[[2/3*Lls+Lms,0,0,Lms,0,0,0],[0,2/3*Lls+Lms,0,0,Lms,0,0],[0,0,Lls/3,0,0,0,0],
                    [Lms,0,0,2/3*a^2*Llr+Lms,0,0,0],[0,Lms,0,0,2/3*a^2*Llr+Lms,0,0],
                    [0,0,0,0,0,a^2*Llr/3,0],[0,0,0,0,0,0,J]]):
Gfull := Matrix(7,7): Gfull[1..6,1..6] := Lp: Gfull[7,7] := J:
Cq := M . Gfull . Transpose(M):
cnt := 0:
for i to 7 do for j to 7 do
  if Z(Cq[i,j] - Cexp[i,j]) <> 0 then cnt := cnt + 1 fi:
od: od:
printf("C1  count: components g(v_a,v_b) differing from array (7.1), theta0 symbolic = %d\n", cnt):
cnt := 0:
for k to 7 do
  Rq := Pushforward(Phiinv, R[k]):
  Rq := evalDG(subs({x = Bv[1], y = Bv[2], a1 = Av[1], a2 = Av[2], a3 = Av[3], a4 = Bv[3], phi = th}, Rq)):
  if map(Z, DGinfo(LieDerivative(Rq, gm), "CoefficientSet")) minus {0} <> {} then
    cnt := cnt + 1: printf("C2  R%d on Q is not Killing\n", k):
  fi:
  if k = 7 then
    R7Q := Rq:
    printf("C2  R7 on Q = %a\n", zc(R7Q, dQ)):
    cntc := 0:
    for i to 7 do if map(Z, zc(LieBracket(R7Q, v[i]), dQ)) <> [0$7] then cntc := cntc + 1 fi: od:
    printf("C2  count: qd0 fields not commuting with R7 on Q = %d\n", cntc):
  fi:
od:
printf("C2  count: right-invariant generators that fail to be Killing for g = %d\n", cnt):
Om := 1/sqrt(3)*Matrix([[0,-1,1],[1,0,-1],[-1,1,0]]):
qrv := Om . Vector([qra,qrb,qrc]):
Yminus := evalDG(DX[7] - qrv[1]*DX[4] - qrv[2]*DX[5] - qrv[3]*DX[6]):
printf("C3  R7 - Y_minus (Wolfram's Killing field) = %a\n", map(Z, zc(evalDG(R7Q - Yminus), dQ))):
cnt := 0:
for k to 7 do if map(Z, DGinfo(LieDerivative(v[k], gm), "CoefficientSet")) minus {0} <> {} then cnt := cnt + 1 fi: od:
printf("C4  qd0 fields that are not Killing (left- but not bi-invariant metric expected, nonzero) = %d\n", cnt):
