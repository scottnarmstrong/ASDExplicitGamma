module

public import ASDExplicitGamma.Scalar.DropHomogeneity

/-! Generic norm bounds for the four resolvent terms. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open scoped InnerProduct InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem drop_g1_bounds (B J N C : H →L[ℝ] H) (f : H) {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    (hB : ‖B‖ ≤ β) (hN : ‖N‖ ≤ β) (hC : ‖C‖ ≤ κ) :
    ‖hilbertG1LinearTerm B J f C‖ ≤ ‖J‖ * (β * ‖f‖) ^ 2 * κ ∧
    ‖hilbertG1HessianTerm B J f C‖ ≤ ‖J‖ * (β * ‖f‖) ^ 2 * (κ * β * κ) ∧
    ‖hilbertG1CubicTerm B J f C‖ ≤ ‖J‖ * (β * ‖f‖) ^ 2 * (κ * β * κ * β * κ) ∧
    ‖hilbertG1QuarticTerm B J f C N‖ ≤ ‖J‖ * (β * ‖f‖) ^ 2 * (κ * β * κ) ^ 2 * β := by
  set b : ℝ := β * ‖f‖ with hb
  have hb0 : 0 ≤ b := mul_nonneg hβ (norm_nonneg f)
  have hu : ‖B f‖ ≤ b := (B.le_opNorm f).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg f))
  have hJu : ‖J (B f)‖ ≤ ‖J‖ * b :=
    (J.le_opNorm _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg J))
  have hCBC : ‖C * B * C‖ ≤ κ * β * κ := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hC hB (norm_nonneg _) hκ)) hC (norm_nonneg _) (by positivity))
  have hCBCBC : ‖C * B * C * B * C‖ ≤ κ * β * κ * β * κ := by
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
      (mul_le_mul hCBC hB (norm_nonneg _) (by positivity))) hC (norm_nonneg _) (by positivity))
  have hs : ‖(C * B * C) (B f)‖ ≤ (κ * β * κ) * b :=
    ((C * B * C).le_opNorm _).trans
      (mul_le_mul hCBC hu (norm_nonneg _) (by positivity))
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc ‖hilbertG1LinearTerm B J f C‖ ≤ ‖J (B f)‖ * ‖C (B f)‖ := by
          unfold hilbertG1LinearTerm
          rw [norm_neg]
          exact (abs_real_inner_le_norm _ _)
      _ ≤ (‖J‖ * b) * (κ * b) := by
          refine mul_le_mul hJu ?_ (norm_nonneg _) (by positivity)
          exact (C.le_opNorm _).trans (mul_le_mul hC hu (norm_nonneg _) hκ)
      _ = ‖J‖ * b ^ 2 * κ := by ring
  · calc ‖hilbertG1HessianTerm B J f C‖ ≤ ‖J (B f)‖ * ‖(C * B * C) (B f)‖ := by
          unfold hilbertG1HessianTerm
          exact (abs_real_inner_le_norm _ _)
      _ ≤ (‖J‖ * b) * ((κ * β * κ) * b) :=
          mul_le_mul hJu hs (norm_nonneg _) (by positivity)
      _ = ‖J‖ * b ^ 2 * (κ * β * κ) := by ring
  · calc ‖hilbertG1CubicTerm B J f C‖ ≤ ‖J (B f)‖ * ‖(C * B * C * B * C) (B f)‖ := by
          unfold hilbertG1CubicTerm
          rw [norm_neg]
          exact (abs_real_inner_le_norm _ _)
      _ ≤ (‖J‖ * b) * ((κ * β * κ * β * κ) * b) := by
          refine mul_le_mul hJu ?_ (norm_nonneg _) (by positivity)
          exact ((C * B * C * B * C).le_opNorm _).trans
            (mul_le_mul hCBCBC hu (norm_nonneg _) (by positivity))
      _ = ‖J‖ * b ^ 2 * (κ * β * κ * β * κ) := by ring
  · set t := (C * B * C) (B f) with ht
    calc ‖hilbertG1QuarticTerm B J f C N‖ ≤ ‖J t‖ * ‖N t‖ := by
          unfold hilbertG1QuarticTerm
          exact (abs_real_inner_le_norm _ _)
      _ ≤ (‖J‖ * ((κ * β * κ) * b)) * (β * ((κ * β * κ) * b)) := by
          refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
          · exact (J.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg J))
          · exact (N.le_opNorm _).trans (mul_le_mul hN hs (norm_nonneg _) hβ)
      _ = ‖J‖ * b ^ 2 * (κ * β * κ) ^ 2 * β := by ring

end

end ASDExplicitGamma.Scalar
