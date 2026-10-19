# A Lean check of the algebra

`LeanCheck.lean` proves, in Lean 4 with mathlib, nineteen statements that the manuscript's
proofs rest on. Every one compiles and none uses `sorry`: `#print axioms` reports only
`propext`, `Classical.choice` and `Quot.sound` for all nineteen, which is the standard mathlib
base.

## What this does and does not check

**It checks the algebra.** The identities below are the ones `MapleScripts/*.mpl` verify, now
proved from the axioms of an ordered field rather than evaluated by a computer algebra system.
Where Maple reports that an expression simplifies to zero, Lean produces a proof term.

**It does not check the geometry, which is where the mathematics of the paper lives.** The
brackets of the seven qd0 vector fields, the non-integrability of the frame, Noether's theorem
for Hamel's equations, Liouville integrability, the Euler-Poincaré reduction and the automorphism
action of a moving frame are all untouched. Mathlib has manifolds and Lie algebras, and it has
neither Hamel's equations nor the Euler-Poincaré reduction nor Liouville-Arnold, so formalising
those means building the theory first. That is a project, not a check.

**The transcription is the weak link.** Lean verifies that the statements in this file follow
from the axioms. It cannot verify that they are the manuscript's statements. Read each theorem
against the equation it names before trusting it.

## What is proved

| Lean name | Manuscript | Statement |
|---|---|---|
| `br_J_P₁`, `br_J_P₂`, `br_P₁_P₂` | Thm 4.1 | the `𝔰𝔢(2)` bracket table, on matrices realising `v₇, v₄, v₅` |
| `delta_pos` | `integrability_check.mpl` chk8 | `Δ = μs μr − Lms² > 0` for positive inductances |
| `Te_odd`, `Te_zero` | Thm 9.2 | the torque–slip curve is odd and vanishes at zero slip |
| `Te_at_critical` | Thm 9.2 | the curve attains `T_max` at `σ = ρ`, for every positive `ρ` |
| `Te_le` | Thm 9.2 | `T_max` bounds the curve everywhere |
| `twoIdentities` | eq. (81) | the two identities the Routh–Hurwitz reduction uses |
| `div_pos_iff_num` | Thm 9.3 | the positive denominator does not change the sign of `c₀` |
| `c₀_pos_iff` | Thm 9.3 | `c₀ > 0` exactly when `\|σ\| < ρ`, the rising branch |
| `remainder_pos` | eq. (80) | the Routh–Hurwitz remainder is positive with no further hypothesis |
| `charpoly_factors` | §11, P2 | at no load the cubic factors as `(s+ρ)(s²+ρs+k λ₀)` |
| `stiffness_eq` | §11, P3 | the stiffness of that quadratic is `2 T_max / J` |
| `kappa_eq_two_Tmax` | §11, P4 | at zero slip the pendulum's restoring torque is `2 T_max` |
| `underdamped_iff` | §11, P5 | the oscillation condition |
| `decay_rate` | §11, P5 | completing the square gives the decay rate `ρ/2` |
| `power_balance` | §11 | speed-voltage power cancels torque power in the machine's own array |
| `antisymm_contract` | §11 | an array antisymmetric in its lower indices annihilates `ξ^i ξ^j` |

`c₀_pos_iff` is stated on the numerator, with `div_pos_iff_num` supplying the step to the
quotient, which keeps both proofs free of case analysis on the denominator.

## Running it

```sh
cd ~/Claude_Projects/Research/Hamel/LeanCheck
~/.elan/bin/lake build
```

Mathlib is a dependency pinned to `master` in `lakefile.toml`; `lake build` fetches its cache.
`.lake/` is not tracked. First build takes a few minutes, later ones seconds.

To re-audit for `sorry`:

```sh
P=$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':').lake/build/lib/lean
LEAN_PATH=$P ~/.elan/bin/lean /path/to/a/file/that/imports/LeanCheck/and/prints/axioms.lean
```

Written 2026-09-14 against Lean 4.34.0.
