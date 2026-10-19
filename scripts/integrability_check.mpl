# Integrability of the free machine --- verification of Section 8 of manuscript/main.tex
# Checks, against the qd0 array (eq:gframe) and the equations of motion (eq:eom1)-(eq:eom7):
#   the torque identity, the energy (eq:energy), conservation of zeta (eq:zeta) and of E,
#   the pendulum (eq:pendulum), the driven lossless case (eq:washboard), Delta > 0,
#   and the rotor-row identity K(-th) = e^{-i th} K(0) behind the phasor zeta.
# Every printed chk must be 0; chk8 must be manifestly positive.  Written 2026-09-13.
restart:
G := Matrix([[mus,0,Lms,0],[0,mus,0,Lms],[Lms,0,mur,0],[0,Lms,0,mur]]):
X := LinearAlgebra:-LinearSolve(G, Vector([lqs,lds,lqr,ldr])):
x1:=X[1]: x2:=X[2]: x4:=X[3]: x5:=X[4]:
Delta := mus*mur - Lms^2:
chk1 := simplify(Lms*(x1*x5 - x2*x4) - Lms/Delta*(lqs*ldr - lds*lqr));
lel := simplify(1/2*LinearAlgebra:-Transpose(X).G.X):
V := (mur*(lqs^2+lds^2) + mus*(lqr^2+ldr^2))/(2*Delta) - Lms/Delta*(lqs*lqr + lds*ldr):
chk2 := simplify(lel - V);
sys := {diff(qs(t),t)=0, diff(ds(t),t)=0, diff(qr(t),t) = om(t)*dr(t),
        diff(dr(t),t) = -om(t)*qr(t), diff(th(t),t)=om(t)}:
S := [lqs=qs(t),lds=ds(t),lqr=qr(t),ldr=dr(t)]:
chk3 := simplify(eval(diff((qr(t)+I*dr(t))*exp(I*th(t)),t), sys));
E := J*om(t)^2/2 + eval(V,S):
chk4 := simplify(eval(eval(diff(E,t), sys), diff(om(t),t)=eval(Lms*(x1*x5 - x2*x4), S)/J));
chk5 := simplify(expand(Lms/Delta*(sig*cos(al)*rho*sin(ph-th) - sig*sin(al)*rho*cos(ph-th))
                        + Lms*sig*rho/Delta*sin(th - (ph-al))));
chk6 := simplify(expand(-Lms/Delta*(sig*cos(al)*rho*cos(ph-th)+sig*sin(al)*rho*sin(ph-th))
                        + Lms*sig*rho/Delta*cos(th-(ph-al))));
chk7 := simplify(expand(Lms/Delta*(sig*cos(al-ws*t)*rho*sin(ph-th) - sig*sin(al-ws*t)*rho*cos(ph-th))
                        + Lms*sig*rho/Delta*sin(th - ws*t - (ph-al))));
chk8 := expand(eval(Delta, [mus=2/3*Lls+Lms, mur=2/3*a^2*Llr+Lms]));
Kb := b -> 2/3*Matrix([[cos(b), cos(b-2*Pi/3), cos(b+2*Pi/3)],[sin(b), sin(b-2*Pi/3), sin(b+2*Pi/3)]]):
chk9 := [seq(simplify(convert(Kb(-vth)[1,k] + I*Kb(-vth)[2,k] - exp(-I*vth)*(Kb(0)[1,k]+I*Kb(0)[2,k]), exp)), k=1..3)];
