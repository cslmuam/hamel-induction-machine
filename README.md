# Euler–Poincaré reduction and moving trivialisations for the qd0 induction machine

Computational supplement to the article of the same title by César S. López-Monsalvo, Irvin
López-García and David Decena-Ortega (Universidad Autónoma Metropolitana – Azcapotzalco),
submitted to *Communications in Analysis and Mechanics*.

Every result of the article is proved in its text. The files here check the symbolic identities
those proofs use, formalise the algebraic identities they rest on, and regenerate the data of the
three figures.

## Contents

| Path | What it is |
|---|---|
| `scripts/*.mpl` | Maple checks (Maple 2021) |
| `scripts/*.wls` | Wolfram Language checks and figure computation (Mathematica 14.3, run with `wolframscript`) |
| `scripts/*.out` | the transcript of the run of each script |
| `manuscript/fig_synthetic_data.tex` | the figure data, written by `scripts/synthetic_figures.wls` |
| `manuscript/figure_*.tex`, `figure_*.pdf` | stand-alone TikZ sources of Figures 1–3 and their PDFs |
| `lean/` | Lean 4 formalisation of the algebraic identities, with its own `README.md` |

## Which file checks which result

Numbers refer to the article as submitted.

| Result | File |
|---|---|
| Theorem 3.2 (non-integrability of the qd0 frame), Remark 3.3, Theorem 4.1 (the Lie algebra), Proposition 4.2 (the Lie group) | `scripts/liegroup_check.mpl` |
| Theorem 6.3 (the equations of motion), Proposition 8.1 (the conserved linkages) | `scripts/integrability_check.mpl` |
| Proposition 6.1, Theorem 7.1 (the bracket of the moving frame), Remark 7.2, Proposition 7.3, Lemma 7.4, Theorem 7.5 | `scripts/rotating_frame_check.wls` |
| Proposition 4.3 (automorphisms of the reference angle), Remark 7.2, Theorem 7.6 (the reduction under a varying rate) | `scripts/varying_rate_check.wls` |
| intermediate identities in the proofs of Propositions 6.1, 8.1 and 8.2 | `scripts/prose_identities_check.wls` |
| Figures 1–3 | `scripts/synthetic_figures.wls` |
| the bracket table of the Euclidean algebra in the proof of Theorem 4.1, the positivity of Δ in Section 8, the power balance, and the vanishing of the contraction in equation (46) | `lean/LeanCheck.lean`, theorems `br_J_P₁`, `br_J_P₂`, `br_P₁_P₂`, `delta_pos`, `power_balance`, `antisymm_contract` |

The headers of the scripts, and `lean/README.md`, cite results by the numbering of an earlier,
longer manuscript from which the article was drawn. The table above gives the numbering of the
article. The Lean file also contains statements used by a companion manuscript on the dynamics of
the machine, which the article does not need.

## Reading the transcripts

Each check prints the number of failures it found, in lines containing `count`, or the value of
an expression that must simplify to zero, in lines `chkN := 0`. Every such line reads 0. The one
exception is `chk8` in `integrability_check.mpl`, which prints Δ as a sum of positive terms.

`synthetic_figures.out` records the numbers quoted in the caption of Figure 2 and used in Figures 1
and 3. The libration period is 0.1194 s. The driven equations integrated in the moving frame agree
with the stationary solution transported by the automorphism curve to within 5.5 × 10⁻⁹ in the
uniformly turning frame and 2.7 × 10⁻⁹ in the frame of varying rate. The drifts of the stator
linkage, the rotor linkage referred to the rotor, the energy and the rotational charge are at most
1.1 × 10⁻⁸.

## Parameters of the figures

The figures use the inductances and inertia of the 3 hp machine of Table 4.10-1 in P. C. Krause,
O. Wasynczuk and S. D. Sudhoff, *Analysis of Electric Machinery and Drive Systems*, 2nd edition
(IEEE Press and Wiley–Interscience, 2002), in a two-pole machine, in SI units. The leakage
inductances are L_ls = L_lr = 0.002 H, the magnetising inductance is L_ms = 0.046 H, the turns
ratio is a = 1 and the inertia is J = 0.089 kg m². The initial state is λ_qs = 0.9, λ_ds = 0.35,
λ_qr = 0.7, λ_dr = −0.2 (in Wb), ϑ = 0.4 rad and dϑ/dt = 2.0 rad/s. The integration uses
`MaxStepSize -> 0.0002` with accuracy and precision goals of 12 digits. All values are set at the
top of `scripts/synthetic_figures.wls`.

## Running

```
maple scripts/liegroup_check.mpl
maple scripts/integrability_check.mpl
wolframscript -file scripts/rotating_frame_check.wls
wolframscript -file scripts/varying_rate_check.wls
wolframscript -file scripts/prose_identities_check.wls
wolframscript -file scripts/synthetic_figures.wls      # rewrites manuscript/fig_synthetic_data.tex
cd manuscript && pdflatex figure_frames.tex            # likewise figure_stationary, figure_charge
cd lean && lake exe cache get && lake build
```

The Lean project pins Lean 4.34.0 in `lean/lean-toolchain` and mathlib at commit
`db1c5741da0acf96c97584de6ccf0e3bfbc0ae99` in `lean/lake-manifest.json`. `lake build` fetches
mathlib, which is distributed under the Apache 2.0 licence.

## Licence

The files of this repository are released under the MIT licence, in `LICENSE`. The Lean project
depends on mathlib, which is released under the Apache 2.0 licence.
