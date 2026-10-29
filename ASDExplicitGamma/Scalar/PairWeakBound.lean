module

public import ASDExplicitGamma.Scalar.PairWeakParent

/-! The tiled weak energy of the pair-space (two-slot) solution `B_old s` of a two-slot source
`(F, G)`: `W(∇φ) + W(∇η) ≤ ((1 + 3^{-1/4}) B*)² (P(F) + P(G))`, with the exact constant
`D = 1 + 3^{-1/4}` of the source (no loss against the certified `44/25`). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem avg_sq_nonneg (Q : TriadicCube 2) (n : ℕ) (u : TriadicCube 2 → ℝ) :
    0 ≤ descendantsAverage Q n (fun U => u U ^ 2) := by
  unfold descendantsAverage
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => sq_nonneg _)

/-- Cauchy–Schwarz for the finite tile averages. -/
theorem avg_mul_le (Q : TriadicCube 2) (n : ℕ) (u v : TriadicCube 2 → ℝ) :
    descendantsAverage Q n (fun U => u U * v U) ≤
      Real.sqrt (descendantsAverage Q n (fun U => u U ^ 2)) *
        Real.sqrt (descendantsAverage Q n (fun U => v U ^ 2)) := by
  have hu := avg_sq_nonneg Q n u
  rw [← Real.sqrt_mul hu]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  unfold descendantsAverage
  set N : ℝ := ((descendantsAtDepth Q n).card : ℝ)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (descendantsAtDepth Q n) u v
  have hN : 0 ≤ N⁻¹ := by positivity
  calc (N⁻¹ * ∑ U ∈ descendantsAtDepth Q n, u U * v U) ^ 2
      = (N⁻¹) ^ 2 * (∑ U ∈ descendantsAtDepth Q n, u U * v U) ^ 2 := by ring
    _ ≤ (N⁻¹) ^ 2 * ((∑ U ∈ descendantsAtDepth Q n, u U ^ 2) *
        (∑ U ∈ descendantsAtDepth Q n, v U ^ 2)) :=
      mul_le_mul_of_nonneg_left cs (sq_nonneg _)
    _ = _ := by ring

/-- Minkowski for the finite tile averages. -/
theorem avg_minkowski (Q : TriadicCube 2) (n : ℕ) (u v : TriadicCube 2 → ℝ) :
    descendantsAverage Q n (fun U => (u U + v U) ^ 2) ≤
      (Real.sqrt (descendantsAverage Q n (fun U => u U ^ 2)) +
        Real.sqrt (descendantsAverage Q n (fun U => v U ^ 2))) ^ 2 := by
  have hu := avg_sq_nonneg Q n u
  have hv := avg_sq_nonneg Q n v
  have hexp : descendantsAverage Q n (fun U => (u U + v U) ^ 2) =
      descendantsAverage Q n (fun U => u U ^ 2) +
        2 * descendantsAverage Q n (fun U => u U * v U) +
        descendantsAverage Q n (fun U => v U ^ 2) := by
    have : (fun U => (u U + v U) ^ 2) =
        fun U => (u U ^ 2 + 2 * (u U * v U)) + v U ^ 2 := by
      funext U; ring
    rw [this, descendantsAverage_add, descendantsAverage_add, descendantsAverage_mul_left]
  rw [hexp]
  have h := avg_mul_le Q n u v
  have e1 := Real.sq_sqrt hu
  have e2 := Real.sq_sqrt hv
  nlinarith [h, e1, e2]

/-- Pointwise Cauchy step: two squared sums combine into one square. -/
theorem two_comp_sq (p q a b v : ℝ) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = v ^ 2) :
    (p + a) ^ 2 + (q + b) ^ 2 ≤ (Real.sqrt (p ^ 2 + q ^ 2) + v) ^ 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ p ^ 2 + q ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (p ^ 2 + q ^ 2)
  have hcs : (p * a + q * b) ^ 2 ≤ (p ^ 2 + q ^ 2) * v ^ 2 := by
    rw [← hab]; nlinarith [sq_nonneg (p * b - q * a)]
  have hle : p * a + q * b ≤ Real.sqrt (p ^ 2 + q ^ 2) * v := by
    have h2 := Real.abs_le_sqrt hcs
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv] at h2
    exact (le_abs_self _).trans h2
  nlinarith [hs, hle, hab]

end

end ASDExplicitGamma.Scalar
