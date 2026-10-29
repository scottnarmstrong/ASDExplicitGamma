module

public import ASDExplicitGamma.Native.OldSignedGenericShortMean
public import ASDExplicitGamma.Native.OldSignedInitialMeanTail

/-! Generic first moments on the finite initial-law prefix, with a complete tail budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- Actual first moments on the initial depth-five prefix use only generic
producers at earlier native cutoffs. -/
theorem old_signed_initial_mean_prefix_pointwise
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (j : ℕ) (hj : j<65) :
    (∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*((7/50:ℝ)+(3/500)*(j:ℝ)) := by
  have hh := old_signed_initial_generic_depth_mean M h hM hg n hpast (5+j) (by omega) (by omega)
  have hnum := old_signed_generic_short_mean (5+j) (by omega)
  have hfin := hh.trans (mul_le_mul_of_nonneg_left hnum (cold_theta_pos M).le)
  convert hfin using 1
  push_cast
  ring

/-- Complete sum of the rational affine-geometric prefix majorant. -/
theorem old_signed_initial_mean_prefix_hasSum :
    HasSum (fun j : ℕ => ((7/50:ℝ)+(3/500)*(j:ℝ))*(29/50:ℝ)^j)
      ((7/50)/(1-29/50)+(3/500)*(29/50)/(1-29/50)^2) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(29/50:ℝ)‖<1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(29/50:ℝ)‖<1)
  convert (h0.mul_left (7/50:ℝ)).add (h1.mul_left (3/500:ℝ)) using 1
  · funext j; ring
  · ring

/-- The entire finite prefix is paid before adding the independently
controlled infinite tail; no equality at a finite truncation is used. -/
theorem old_signed_initial_mean_prefix_sum
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) :
    (∑ j ∈ Finset.range 65,inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)) ≤
      theta M*((7/50)/(1-29/50)+(3/500)*(29/50)/(1-29/50)^2) := by
  let g := fun j : ℕ => ((7/50:ℝ)+(3/500)*(j:ℝ))*(29/50:ℝ)^j
  have hθ := (cold_theta_pos M).le
  have hsum : (∑ j ∈ Finset.range 65,inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)) ≤
      ∑ j ∈ Finset.range 65,theta M*g j := by
    apply Finset.sum_le_sum
    intro j hj
    have hmean := old_signed_initial_mean_prefix_pointwise M h hM hg n hpast j (Finset.mem_range.mp hj)
    have hw := (old_signed_weighted_mean_depth_weight M hg j).trans
      (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤(289/500)*(1001/1000))
        (by norm_num : (289/500:ℝ)*(1001/1000)≤29/50) j)
    have hh := mul_le_mul hw hmean
      (integral_nonneg (cutoffTraceDefect_nonneg _ _ _)) (by positivity : (0:ℝ)≤(29/50)^j)
    exact hh.trans_eq (by dsimp [g]; ring)
  rw [←Finset.mul_sum] at hsum
  have hgeo := old_signed_initial_mean_prefix_hasSum
  have hh := hgeo.summable.sum_le_tsum (Finset.range 65) (fun j _ => by positivity)
  rw [hgeo.tsum_eq] at hh
  exact hsum.trans (mul_le_mul_of_nonneg_left hh hθ)

end
end ASDExplicitGamma.Native
