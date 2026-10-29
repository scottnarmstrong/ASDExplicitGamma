module

-- Ported from GMCExplicitDelta Contract/DerivedGeometry.lean (Apache-2.0).

public import ASDExplicitGamma.Triadic.Support.Contract.Row
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Contract layer: Haar exponents, cutoff geometry and localization (row-only constants)

§3.3 items 1, 2, 9 and the constants of H9–H13. Every quantity here depends on the row
only (not on `δ, D, F`), so it is the same at every disorder `δ_λ` (R4(e)).

Conventions. `π` is `Real.pi`; `3^r` with real `r` is `Real.rpow`; infinite series are exact
`tsum`s (the truncation `K_H` and the geometric tails of H12 are the numerics layer's job).
A `tsum` of a non-summable family is `0` in Lean; every series below is summable on the carrier
of the obligations (`0 < s < 1/2` gives `q_s < 3`, `u_s < 3`, and H12 bounds `b_k`), which the
analytic layer proves.

The formulas are the explicit constants of the descendant geometry (sharp version for `d ≥ 3`) and
of the localization estimate.
-/

@[expose] public section

open Real

namespace ASDExplicitGamma.Triadic.Support.Contract

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### Item 1: Haar exponents and the history ratio -/

/-- `q_s = 3^{2s}`. -/
noncomputable def qs : ℝ := (3 : ℝ) ^ (2 * (row.s : ℝ))

/-- `w = 3^{-2s} = q_s^{-1}`. -/
noncomputable def wHaar : ℝ := (3 : ℝ) ^ (-(2 * (row.s : ℝ)))

/-- The history ratio `x = 3^{-2s+d/32}` (§1.7, §3.3 item 1). -/
noncomputable def xHist : ℝ := (3 : ℝ) ^ (-(2 * (row.s : ℝ)) + (d : ℝ) / 32)

/-- `C₀ = (1-w)/(1-x)`. Meaningful for `x < 1`, i.e. `2s > d/32` (O.par.1). -/
noncomputable def C0 : ℝ := (1 - row.wHaar) / (1 - row.xHist)

/-- `C₁ = C₀ x = (1-w)∑_{r≥1} x^r`. -/
noncomputable def C1 : ℝ := row.C0 * row.xHist

/-! ### Item 2: good-event radius and descendant ellipticity -/

end Row

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### H7, H10: the cutoff and its constant mode -/

end Row

/-! ### H9, H14: the geometric minimum series -/

namespace Row

variable {d : ℕ} (row : Row d)

/-! ### H9: multiplier coefficients of the Haar blocks -/

/-! ### H12: Haar sums and geometric tails -/

/-! ### H13: localization weights -/

end Row

end ASDExplicitGamma.Triadic.Support.Contract
