module

public import ASDExplicitGamma.Native.OldSignedWhiteAbsoluteCovariance

/-! Complete spatial covariance passage under the sharp product majorant.
This permits the actual L2 reciprocal error to test an L2 harmonic kernel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
noncomputable section

/-- Integrated covariance with the actual product majorant, retaining
arbitrary correlations between both kernels and the spatial multiplier. -/
theorem old_signed_weighted_white_covariance_product {X H I : Type*}
    [MeasurableSpace X] (mu : Measure X) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Countable I]
    (e : HilbertBasis I ℝ H) (A B : X → H) (r : X → ℝ)
    (hA : AEStronglyMeasurable A mu) (hB : AEStronglyMeasurable B mu)
    (hr : AEStronglyMeasurable r mu)
    (hi : Integrable (fun x => |r x| *‖A x‖*‖B x‖) mu) :
    HasSum (fun n => ∫ x,r x*inner ℝ (e n) (A x)*inner ℝ (e n) (B x) ∂mu)
      (∫ x,r x*inner ℝ (A x) (B x) ∂mu) := by
  let bound : I → X → ℝ := fun n x => |r x| *|inner ℝ (e n) (A x)*inner ℝ (e n) (B x)|
  have hm n : AEStronglyMeasurable (bound n) mu := by
    convert hr.norm.mul (((hA.const_inner (𝕜 := ℝ) (c := e n)).mul
      (hB.const_inner (𝕜 := ℝ) (c := e n))).norm) using 1
  have hs x : Summable (fun n => bound n x) :=
    (old_signed_white_absolute_tsum_le e (A x) (B x)).1.mul_left |r x|
  apply hasSum_integral_of_dominated_convergence bound
  · intro n
    exact (hr.mul (hA.const_inner (𝕜 := ℝ) (c := e n))).mul (hB.const_inner (𝕜 := ℝ) (c := e n))
  · intro n
    filter_upwards with x
    dsimp only [bound]
    simp only [Real.norm_eq_abs,abs_mul,mul_assoc,le_refl]
  · exact Filter.Eventually.of_forall hs
  · apply hi.mono' ((AEMeasurable.tsum (fun n => (hm n).aemeasurable)).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
    change (∑' n,|r x| *|inner ℝ (e n) (A x)*inner ℝ (e n) (B x)|)≤_
    rw [tsum_mul_left,mul_assoc]
    exact mul_le_mul_of_nonneg_left (old_signed_white_absolute_tsum_le e (A x) (B x)).2 (abs_nonneg _)
  · filter_upwards with x
    have hh := (e.hasSum_inner_mul_inner (A x) (B x)).mul_left (r x)
    simpa only [real_inner_comm (A x),mul_assoc] using hh

end
end ASDExplicitGamma.Native
