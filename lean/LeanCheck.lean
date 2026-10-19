/-
  Machine-checked algebra behind `manuscript/main.tex`.

  Scope, stated plainly.  The manuscript's proofs are differential geometric: brackets of
  vector fields on a seven dimensional manifold, Noether's theorem for Hamel's equations,
  Liouville integrability, the Euler-Poincare reduction.  None of that is formalised here, and
  mathlib carries no Euler-Poincare or Liouville-Arnold machinery to build it on.  What this
  file checks is the algebra those proofs rest on, the same identities that
  `MapleScripts/*.mpl` verify, now in a proof assistant and independent of the computer algebra
  system.

  Numbering follows the manuscript as it stands (33 numbered results, 12 sections).
-/
import Mathlib

namespace Hamel

open scoped Matrix

/-! ## 1.  The Euclidean summand of Theorem 4.1

The manuscript claims the qd0 frame closes on `ℝ⁴ ⊕ 𝔰𝔢(2)`, with `v₇` the rotation generator
and `v₄, v₅` the translations.  Realise those three generators as matrices and check the
bracket table.  The abelian summand needs no check beyond its brackets vanishing, which is
`rfl` for scalar multiples of the zero matrix and is not restated. -/

/-- The rotation generator of `𝔰𝔢(2)`, the image of `v₇`. -/
def J : Matrix (Fin 3) (Fin 3) ℝ := !![0, -1, 0; 1, 0, 0; 0, 0, 0]

/-- The first translation generator, the image of `v₄`. -/
def P₁ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 0; 0, 0, 0]

/-- The second translation generator, the image of `v₅`. -/
def P₂ : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 1; 0, 0, 0]

/-- Commutator of matrices, written out to avoid depending on a `LieRing` instance. -/
def br (A B : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ := A * B - B * A

theorem br_J_P₁ : br J P₁ = P₂ := by
  simp only [br, J, P₁, P₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem br_J_P₂ : br J P₂ = -P₁ := by
  simp only [br, J, P₁, P₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The two translations commute, which is what makes the summand `𝔰𝔢(2)` and not
`𝔰𝔩(2)`. -/
theorem br_P₁_P₂ : br P₁ P₂ = 0 := by
  simp only [br, P₁, P₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-! ## 2.  The machine constants

`μs`, `μr` are the self inductances of the two members, `Lms` the mutual inductance, `Δ` the
determinant of the inductance array, `J` the inertia.  Everything below is stated for positive
inductances, which is postulate (C1) together with the physical sign of an inductance. -/

variable {Lls Llr Lms a μs μr Δ Jm ρ σ ls : ℝ}

/-- `Δ = μs μr - Lms²` is positive for a machine, which the manuscript needs for the
inductance array to be invertible (`integrability_check.mpl`, `chk8`). -/
theorem delta_pos (hLls : 0 < Lls) (hLlr : 0 < Llr) (hLms : 0 < Lms) (ha : a ≠ 0)
    (hμs : μs = (2 / 3) * Lls + Lms) (hμr : μr = (2 / 3) * a ^ 2 * Llr + Lms) :
    0 < μs * μr - Lms ^ 2 := by
  have ha2 : 0 < a ^ 2 := by positivity
  subst hμs hμr
  nlinarith [mul_pos hLls hLlr, mul_pos ha2 hLlr, mul_pos hLms hLls,
    mul_pos (mul_pos ha2 hLlr) hLms, sq_nonneg Lms]

/-! ## 3.  Theorem 9.2, the torque-slip curve

`Te σ = 2 T_max ρ σ / (ρ² + σ²)`.  The three claims of the theorem that are algebra: the curve
is odd, it attains `T_max` at the critical slip `σ = ρ`, and `T_max` bounds it everywhere. -/

/-- The torque-slip curve of Theorem 9.2. -/
noncomputable def Te (Tmax ρ σ : ℝ) : ℝ := 2 * Tmax * ρ * σ / (ρ ^ 2 + σ ^ 2)

theorem Te_odd (Tmax ρ σ : ℝ) : Te Tmax ρ (-σ) = -Te Tmax ρ σ := by
  simp only [Te, neg_sq]
  ring

theorem Te_zero (Tmax ρ : ℝ) : Te Tmax ρ 0 = 0 := by
  simp [Te]

/-- At the critical slip the curve attains the breakdown torque, for every positive `ρ`.
This is the sentence of Section 11 that the peak does not move with the rotor resistance:
`ρ` is proportional to it and `T_max` is free of it. -/
theorem Te_at_critical (Tmax : ℝ) (hρ : 0 < ρ) : Te Tmax ρ ρ = Tmax := by
  have h : ρ ^ 2 + ρ ^ 2 ≠ 0 := by positivity
  rw [Te, div_eq_iff h]
  ring

/-- The breakdown torque bounds the curve. -/
theorem Te_le (Tmax : ℝ) (hTmax : 0 < Tmax) (hρ : 0 < ρ) : Te Tmax ρ σ ≤ Tmax := by
  have hd : 0 < ρ ^ 2 + σ ^ 2 := by positivity
  rw [Te, div_le_iff₀ hd]
  nlinarith [sq_nonneg (ρ - σ), hTmax.le]

/-! ## 4.  Theorem 9.3, the Routh-Hurwitz test

At the equilibrium linkage of Theorem 9.2 the components are
`λqr = ρ² lzero / (ρ² + σ²)` and `λdr = ρ σ lzero / (ρ² + σ²)`, and the constant term of the
characteristic polynomial is `c₀ = k (ρ λqr - σ λdr)`.  The theorem turns on the two
identities of equation (81) and on the sign of `c₀`. -/

theorem twoIdentities (lzero : ℝ) (hρ : 0 < ρ) :
    ρ * (ρ ^ 2 * lzero / (ρ ^ 2 + σ ^ 2)) - σ * (ρ * σ * lzero / (ρ ^ 2 + σ ^ 2))
      = ρ * lzero * (ρ ^ 2 - σ ^ 2) / (ρ ^ 2 + σ ^ 2)
    ∧ ρ * (ρ ^ 2 * lzero / (ρ ^ 2 + σ ^ 2)) + σ * (ρ * σ * lzero / (ρ ^ 2 + σ ^ 2))
      = ρ * lzero := by
  have hd : ρ ^ 2 + σ ^ 2 ≠ 0 := by positivity
  constructor <;> field_simp

/-- Dividing by the positive denominator of the equilibrium linkage does not change a sign,
so the test may be read off the numerator. -/
theorem div_pos_iff_num (x : ℝ) (hd : 0 < ρ ^ 2 + σ ^ 2) :
    0 < x / (ρ ^ 2 + σ ^ 2) ↔ 0 < x := by
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact h1
    · linarith
  · intro h
    exact Or.inl ⟨h, hd⟩

/-- Asymptotic stability holds precisely on the rising branch.  With `k`, `lzero` and `ρ`
positive, the constant term `c₀` is positive exactly when `|σ| < ρ`, which is the criterion of
Theorem 9.3. -/
theorem c₀_pos_iff (k lzero : ℝ) (hk : 0 < k) (hl : 0 < lzero) (hρ : 0 < ρ) :
    0 < k * ρ * lzero * (ρ ^ 2 - σ ^ 2) ↔ |σ| < ρ := by
  rw [abs_lt]
  constructor
  · intro h
    have hklr : 0 < k * ρ * lzero := mul_pos (mul_pos hk hρ) hl
    have h2 : 0 < ρ ^ 2 - σ ^ 2 := by
      rcases lt_trichotomy (ρ ^ 2 - σ ^ 2) 0 with hlt | heq | hgt
      · nlinarith
      · rw [heq] at h; simp at h
      · exact hgt
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have h3 : 0 < ρ ^ 2 - σ ^ 2 := by nlinarith
    have hklr : 0 < k * ρ * lzero := mul_pos (mul_pos hk hρ) hl
    exact mul_pos hklr h3

/-- The Routh-Hurwitz remainder is positive without further hypotheses, which is why the
criterion for the cubic reduces to the sign of `c₀` alone. -/
theorem remainder_pos (Tmax : ℝ) (hρ : 0 < ρ) (hJ : 0 < Jm) (hTmax : 0 < Tmax) :
    0 < 2 * ρ * (ρ ^ 2 + σ ^ 2) + 2 * ρ * Tmax / Jm := by
  have h1 : 0 < 2 * ρ * (ρ ^ 2 + σ ^ 2) := by positivity
  have h2 : 0 < 2 * ρ * Tmax / Jm := by positivity
  linarith

/-! ## 5.  The no-load oscillator, prediction 2 of Section 11

This is the prediction promoted from the caption of Figure 6, verified in
`MapleScripts/noload_oscillator_check.mpl` as blocks P1 to P5.  At no load the characteristic
polynomial factors, the stiffness of the surviving quadratic is `2 T_max / J`, and that
stiffness is the restoring torque of the pendulum at zero slip divided by the inertia. -/

/-- P2: at `σ = 0`, `λqr = lzero`, `λdr = 0` the cubic of equation (79) factors. -/
theorem charpoly_factors (k lzero s : ℝ) :
    s ^ 3 + 2 * ρ * s ^ 2 + (ρ ^ 2 + k * lzero) * s + k * ρ * lzero
      = (s + ρ) * (s ^ 2 + ρ * s + k * lzero) := by
  ring

/-- P3: the stiffness of that quadratic is the breakdown torque over the inertia. -/
theorem stiffness_eq (hΔ : Δ ≠ 0) (hμs : μs ≠ 0) (hJ : Jm ≠ 0) :
    (Lms * ls / (Jm * Δ)) * (Lms * ls / μs)
      = 2 * (Lms ^ 2 * ls ^ 2 / (2 * Δ * μs)) / Jm := by
  field_simp

/-- P4: at zero slip the restoring torque of the pendulum is twice the breakdown torque, so
the no-load oscillator is the swing of Section 11 damped by the rotor resistance. -/
theorem kappa_eq_two_Tmax (hΔ : Δ ≠ 0) (hμs : μs ≠ 0) :
    (Lms / Δ) * ls * (Lms * ls / μs) = 2 * (Lms ^ 2 * ls ^ 2 / (2 * Δ * μs)) := by
  field_simp

/-- P5: the oscillator is underdamped precisely below the stated resistance.  The stiffness
`kst` is `2 T_max / J` by `stiffness_eq`, so the condition reads `ρ² < 8 T_max / J`, the proviso
attached to the prediction. -/
theorem underdamped_iff (kst : ℝ) : ρ ^ 2 - 4 * kst < 0 ↔ ρ ^ 2 < 4 * kst := by
  constructor <;> intro h <;> linarith

/-- P5: completing the square exhibits the decay rate `ρ/2`. -/
theorem decay_rate (ωn s : ℝ) :
    s ^ 2 + ρ * s + ωn ^ 2 = (s + ρ / 2) ^ 2 + (ωn ^ 2 - ρ ^ 2 / 4) := by
  ring

/-! ## 6.  The energy balance behind the shared coefficient, Section 11

The rotor rows carry the speed voltages `-ξ⁷ λdr` and `+ξ⁷ λqr`, the mechanical row the torque
`Lms (ξ¹ξ⁵ - ξ²ξ⁴)`.  Contracting each row with its own quasi-velocity, the two cancel.  This
is the identity the manuscript attributes to the antisymmetry of the structure constants, and
the reason a measured mismatch between the two coefficients would falsify the lossless lumped
model. -/

theorem power_balance (x₁ x₂ x₄ x₅ x₇ : ℝ) :
    (x₄ * (-(x₇ * (Lms * x₂ + μr * x₅))) + x₅ * (x₇ * (Lms * x₁ + μr * x₄)))
      + x₇ * Lms * (x₂ * x₄ - x₁ * x₅) = 0 := by
  ring

/-- The general statement: an array antisymmetric in its two lower indices annihilates
`ξ^i ξ^j`.  This is the coordinate-free reason for `power_balance`, and the reason the
manuscript can say the energy balance follows from the structure constants alone. -/
theorem antisymm_contract {n : ℕ} (c : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ)
    (hc : ∀ i j, c i j = -c j i) :
    ∑ i, ∑ j, c i j * ξ i * ξ j = 0 := by
  have key : ∑ i, ∑ j, c i j * ξ i * ξ j = -∑ i, ∑ j, c i j * ξ i * ξ j := by
    calc ∑ i, ∑ j, c i j * ξ i * ξ j
        = ∑ j, ∑ i, c i j * ξ i * ξ j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(c j i * ξ j * ξ i) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
            rw [hc i j]
            ring
      _ = -∑ i, ∑ j, c i j * ξ i * ξ j := by simp
  linarith

end Hamel
