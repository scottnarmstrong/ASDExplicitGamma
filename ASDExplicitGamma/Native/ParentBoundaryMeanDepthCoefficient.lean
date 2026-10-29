module

public import ASDExplicitGamma.Native.ParentBoundaryMeanGeometry
public import ASDExplicitGamma.Native.ParentBoundaryCommonSourceKernel
public import ASDExplicitGamma.Native.ParentBoundaryMeanCoefficientBudget

/-! Exact finite source covariance and mixed-direction budgets for parent cell means. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- Complete finite mean covariance coefficient budget with the source
1.856 constant and no shell-count loss. Every physical variance is bounded
from the actual native state before finite Euclidean aggregation. -/
theorem parent_boundary_mean_depth_mu_sum_source
    (M : ABKModel 2) (h : ℝ) (q n : ℤ) (r : ℕ) (hr : 5 ≤ r) (hqr : q=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) :
    (∑ i : Fin height,((q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2)*
      pureFluxCovarianceMu (pureFluxCovarianceA 0 (r+i.val)) (pureFluxCovarianceB 0 (r+i.val))) ≤
        (232/125:ℝ)*(parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
          (parentBoundaryCommonSourceSpatialClock M.gamma height r 4))^2 := by
  let Q := originCube 2 q
  let b := fun i : Fin height => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))
  let L := fun i : Fin height => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let sigma : ℝ := Annealed.sigmaBar M n
  let A := fun i : Fin height => parentBoundaryCommonRowCoefficient Q Q (b i/sigma) (L i) 0
  have hrow (i : Fin height) : (b i^2/sigma^2)*
      pureFluxCovarianceMu (pureFluxCovarianceA 0 (r+i.val)) (pureFluxCovarianceB 0 (r+i.val)) ≤ (232/125:ℝ)*A i^2 := by
    have hi : q+((r+i.val+1:ℕ):ℤ)=n+((i.val+1:ℕ):ℤ) := by omega
    have hh := parent_boundary_mean_mu_row q (r+i.val+1) (by omega) (b i) sigma
    rw [hi] at hh
    exact hh
  have hnorm := parent_boundary_common_band_row_norm_bound Q Q (fun i => b i/sigma) L
  have hQ : cubeScaleFactor Q ≠ 0 := (zpow_pos (by norm_num : (0:ℝ)<3) q).ne'
  rw [div_self hQ] at hnorm
  simp only [mul_one,one_pow] at hnorm
  have hscale : Q.scale=n-(r:ℤ) := hqr
  have h2 := parent_boundary_common_spatial_clock_cap M h Q n r hscale hstate height 2
  have h4 := parent_boundary_common_spatial_clock_cap M h Q n r hscale hstate height 4
  have hroot : parentBoundaryMeanAColumn (parentBoundaryCommonSpatialClock M h Q n height 2)
      (parentBoundaryCommonSpatialClock M h Q n height 4) ≤
      parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
        (parentBoundaryCommonSourceSpatialClock M.gamma height r 4) := by
    unfold parentBoundaryMeanAColumn
    exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (by positivity))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h4) (by positivity))
  have hnorm' : Real.sqrt (∑ i : Fin height,A i^2) ≤ parentBoundaryMeanAColumn
      (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
      (parentBoundaryCommonSourceSpatialClock M.gamma height r 4) := hnorm.trans hroot
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) hnorm' 2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (A i)))] at hsquare
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  rw [←Finset.mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))

/-- Complete finite mixed-direction mean budget, with its exact source
second spatial clock and the same true starting frame. -/
theorem parent_boundary_mean_depth_k_sum_source
    (M : ABKModel 2) (h : ℝ) (q n : ℤ) (r : ℕ) (hqr : q=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) :
    (∑ i : Fin height,((q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2)*
      lemmaVH2kn (cubeScaleFactor (originCube 2 q)/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
        (cubeScaleFactor (originCube 2 q)/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)) ≤
      parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock M.gamma height r 2 := by
  have hh := parent_boundary_mean_kn_sum M h (originCube 2 q) n height
  simp only [div_pow] at hh
  rw [hh]
  exact mul_le_mul_of_nonneg_left (parent_boundary_common_spatial_clock_cap M h (originCube 2 q) n r hqr hstate height 2)
    (by positivity)

end
end ASDExplicitGamma.Native
