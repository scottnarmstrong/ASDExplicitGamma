module

public import ASDExplicitGamma.Native.ParentRowAffineSourceReturn
public import ASDExplicitGamma.Native.ParentRowMeanSlopeComparison
public import ASDExplicitGamma.Native.ParentRowInitialMeanFields

/-! The actual parent affine bill paid by the exact stored panel fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Response Variational Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- The two proved primitive mean inputs fit the exact stored affine mean. -/
theorem parent_row_mean_envelope_fields (j : Fin 16) (t : ℝ) (ht : 0≤t) :
    nativeSourceGenericMeanProfile gammaZero 1 5+t*parentBoundaryMeanSourceSlope gammaZero (j.val+1)≤
      (parentRowFields j).getD 14 0+(parentRowFields j).getD 11 0*t := by
  have hh := add_le_add (parent_row_generic_initial_mean_le j)
    (mul_le_mul_of_nonneg_left (parent_row_mean_source_slope_field j) ht)
  simpa only [mul_comm t] using hh

/-- The literal affine bill is bounded by the affine part of the certified parent panel.
All mean, inverse-bank, variance, energy and derivative estimates are discharged. -/
theorem parent_row_actual_affine_panel
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (hstate : nativeInductionState M h n)
    (hpast : ∀ k<n,nativeInductionState M h k) (j : Fin 16)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ ω,parentBoundaryBandAffineBill M h n (j.val+1) r t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
    theta M*((parentRowFields j).getD 16 0/2*
      ((parentRowFields j).getD 14 0+(parentRowFields j).getD 11 0*t)+
      2*(parentRowFields j).getD 0 0*((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*((156/5:ℝ)*(parentRowFields j).getD 1 0/9)) := by
  have ha := parent_row_affine_source_return M h hM hg n hstate hpast j r hr U hU t ht0 ht1
  have hm := mul_le_mul_of_nonneg_left (parent_row_mean_envelope_fields j t ht0)
    (div_nonneg (parent_row_y_nonneg j) (by norm_num : (0:ℝ)≤2))
  exact ha.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hm le_rfl) le_rfl)
    (cold_theta_pos M).le)

end
end ASDExplicitGamma.Native
