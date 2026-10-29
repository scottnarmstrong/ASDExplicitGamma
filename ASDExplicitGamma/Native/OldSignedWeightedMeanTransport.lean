module

public import ASDExplicitGamma.Native.OldSignedMeanInitialCarrier

/-! Actual complete inverse-weighted mean transport for the OLD q1 panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Complete first moments during the actual insertion retain both the
initial budget and the full theta-scaled source slope. -/
theorem old_signed_actual_weighted_mean_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      inSourceMeanActual M n (5+j) t) ∧
    (1-inverseHistoryDiscount^2)*(3683/2500:ℝ)*
      (∑' j : ℕ,inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
        inSourceMeanActual M n (5+j) t) ≤ theta M*((23/100:ℝ)+(9/500)*t) := by
  let W := fun j : ℕ => inverseHistoryDiscount^(2*j)*bankDepthFrame M j
  let I := fun j : ℕ => W j*inSourceMeanActual M n (5+j) 0
  let S := fun j : ℕ => W j*oldSignedMeanSourceCap M h n (5+j)
  let F := fun j : ℕ => W j*inSourceMeanActual M n (5+j) t
  let D : ℝ := (1-inverseHistoryDiscount^2)*(3683/2500)
  have hinit := old_signed_initial_weighted_mean M h hM hg n
    (fun l hl => hpast l hl.le) (hpast n le_rfl)
  have hI : Summable I ∧ D*(∑' j,I j)≤(23/100)*theta M := by
    simpa only [I,W,D,old_signed_mean_zero_eq_integral] using hinit
  have hS := old_signed_weighted_mean_source_slope_sum M h n hg (hpast n le_rfl)
  have hSsum : Summable S := hS.1
  have hW0 (j : ℕ) : 0≤W j := mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    (by unfold bankDepthFrame; positivity)
  have hF0 (j : ℕ) : 0≤F j := mul_nonneg (hW0 j) (old_signed_partial_mean_nonneg M n (5+j) t)
  have hcap (j : ℕ) : F j≤I j+t*S j := by
    have hh := mul_le_mul_of_nonneg_left (old_signed_actual_mean_source_transport M h hM hg n
      (fun l hl => hpast l hl.le) (5+j) t ht) (hW0 j)
    exact hh.trans_eq (by dsimp [I,S]; ring)
  have hdom := hI.1.add (hSsum.mul_left t)
  have hsum : Summable F := Summable.of_nonneg_of_le hF0 hcap hdom
  have hh := hsum.tsum_le_tsum hcap hdom
  rw [hI.1.tsum_add (hSsum.mul_left t),tsum_mul_left] at hh
  have hD0 : 0≤D := by
    have ha : inverseHistoryDiscount^2≤1 :=
      pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le
    exact mul_nonneg (sub_nonneg.mpr ha) (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hh hD0
  have hlast := add_le_add hI.2 (mul_le_mul_of_nonneg_left hS.2 ht.1)
  refine ⟨hsum,hscaled.trans ?_⟩
  convert hlast using 1 <;> ring

end
end ASDExplicitGamma.Native
