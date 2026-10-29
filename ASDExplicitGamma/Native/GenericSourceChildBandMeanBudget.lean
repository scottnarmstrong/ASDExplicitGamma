module

public import ASDExplicitGamma.Native.GenericSourceBandCoefficientBudget
public import ASDExplicitGamma.Inverse.SourceChildCovarianceBudget

/-! Sharp mean coefficient budget for the simultaneous physical band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Variational
noncomputable section

/-- Complete covariance sums control the mean generator without the
p20 bracket coefficients. -/
theorem native_source_child_band_mean_coefficient_budget
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ)
    (hstate : nativeInductionState M h n) (d u1 u2 : ℝ)
    (hd : 0 ≤ d) (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) :
    (∑ i ∈ Finset.range height,
      let v := (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2
      v*d+2*v*lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i)*u1+v*pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)*u2) ≤
      nativeSourceRawShellVarianceCap M.gamma height*
        ((height:ℝ)*d+2*(65399707/10^9:ℝ)*u1+(259713047/10^9:ℝ)*u2) := by
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let v := fun i : ℕ => (q3ModelAmplitude M h (n+((i+1:ℕ):ℤ)))^2/
    (Annealed.sigmaBar M n:ℝ)^2
  have hg := M.shellPrefix.gamma_pos.le
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have heq : nativeSourceShellClock M.gamma height=e := by
    dsimp [e,nativeSourceShellClock,nativeSourceRawShellVarianceCap]
    congr 2
    ring
  have hv (i : ℕ) (hi : i ∈ Finset.range height) : v i ≤ e := by
    rw [←heq]
    exact native_source_shell_variance_le_clock M h n height (i+1) hstate
      (by have hh := Finset.mem_range.mp hi; omega)
  have hsums := source_child_covariance_weighted_partial_sums (Finset.range height) v e he hv
  have hsum : (∑ i ∈ Finset.range height, v i) ≤ (height:ℝ)*e := by
    calc
      _ ≤ ∑ _i ∈ Finset.range height, e := Finset.sum_le_sum hv
      _ = (height:ℝ)*e := by simp
  calc
    _ = (∑ i ∈ Finset.range height, v i)*d+
        2*(∑ i ∈ Finset.range height, v i*lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i))*u1+
        (∑ i ∈ Finset.range height, v i*pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i))*u2 := by
      calc
        _ = ∑ i ∈ Finset.range height,
            (v i*d+2*(v i*lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i))*u1+(v i*pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i))*u2) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [v]
          ring
        _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
    _ ≤ ((height:ℝ)*e)*d+2*((65399707/10^9:ℝ)*e)*u1+((259713047/10^9:ℝ)*e)*u2 := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hsum hd)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsums.1 (by norm_num)) hu1))
        (mul_le_mul_of_nonneg_right hsums.2 hu2)
    _ = _ := by ring

end
end ASDExplicitGamma.Native
