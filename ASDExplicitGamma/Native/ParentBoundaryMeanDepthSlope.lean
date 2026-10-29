module

public import ASDExplicitGamma.Native.ParentBoundaryMeanProtectedExpectation
public import ASDExplicitGamma.Native.ParentBoundaryMeanDepthCoefficient
public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryRawProfile

/-! Actual mean generator bounds on the complete weak-row depth range. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The source mean slope on depth5+j, with the exact protected-frame
structural ratio and all second/fourth spatial clocks retained. -/
def parentBoundaryMeanDepthSlope (gamma : ℝ) (height j : ℕ) : ℝ :=
  let b : ℝ := 3683/2500
  let R := (3:ℝ)^(2*gamma*(j:ℝ))
  let F := parentBoundaryCommonRawFactor gamma height (5+j)*parentBoundaryCommonRawBase gamma height (5+j)
  let V := parentBoundaryCommonSourceVariance gamma height
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height (5+j) 2
  let A := parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock gamma height (5+j) 2)
    (parentBoundaryCommonSourceSpatialClock gamma height (5+j) 4)
  2*V*R*b+2*K*R*(b*F)+(232/125:ℝ)*A^2*R^2*(b^2*F)

/-- The source depth slope is nonnegative. -/
theorem parent_boundary_mean_depth_slope_nonneg {gamma : ℝ} (hg : 0 ≤ gamma) (height j : ℕ) :
    0 ≤ parentBoundaryMeanDepthSlope gamma height j := by
  unfold parentBoundaryMeanDepthSlope parentBoundaryCommonSourceVariance
    parentBoundaryMeanKConstant parentBoundaryCommonSourceSpatialClock nativeSourceShellClock
    parentBoundaryCommonRawFactor parentBoundaryCommonRawBase
  positivity

/-- Every actual weak-row observation depth has its complete physical mean
generator sum bounded from proved inputs only. -/
theorem parent_boundary_mean_depth_generator_slope
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q n : ℤ) (j : ℕ) (hqr : q=n-((5+j:ℕ):ℤ)) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : t ≤ 1) :
    (∑ i : Fin height,∫ ω,parentBoundaryMeanShellGenerator M h q n height t i ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      parentBoundaryMeanDepthSlope M.gamma height j := by
  let v := fun i : Fin height => (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ)))^2/(Annealed.sigmaBar M n:ℝ)^2
  let k := fun i : Fin height => lemmaVH2kn
    (cubeScaleFactor (originCube 2 q)/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
    (cubeScaleFactor (originCube 2 q)/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
  let mu := fun i : Fin height => pureFluxCovarianceMu (pureFluxCovarianceA 0 (5+j+i.val)) (pureFluxCovarianceB 0 (5+j+i.val))
  let b : ℝ := 3683/2500
  let F := parentBoundaryBandTraceCap M height (5+j)
  let R := (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-(j:ℤ)):ℝ)
  let E := (3:ℝ)^(2*M.gamma*(j:ℝ))
  let V := parentBoundaryCommonSourceVariance M.gamma height
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock M.gamma height (5+j) 2
  let A := parentBoundaryMeanAColumn (parentBoundaryCommonSourceSpatialClock M.gamma height (5+j) 2)
    (parentBoundaryCommonSourceSpatialClock M.gamma height (5+j) 4)
  have hF : 0 ≤ F := parent_boundary_band_trace_cap_nonneg M height (5+j)
  have hR := parent_boundary_common_protected_frame_depth M n j
  have hR0 : 0 ≤ R := hR.1
  have hv : (∑ i : Fin height,v i) ≤ V := by
    simpa only [v,V,parentBoundaryBandVariance,parentBoundaryCommonSourceVariance,div_pow] using parent_boundary_band_variance_clock M h n height hstate
  have hk : (∑ i : Fin height,v i*k i) ≤ K := parent_boundary_mean_depth_k_sum_source M h q n (5+j) hqr hstate height
  have hmu : (∑ i : Fin height,v i*mu i) ≤ (232/125:ℝ)*A^2 := parent_boundary_mean_depth_mu_sum_source M h q n (5+j) (by omega) hqr hstate height
  have hFeq : F=parentBoundaryCommonRawFactor M.gamma height (5+j)*parentBoundaryCommonRawBase M.gamma height (5+j) := by
    have hh := parent_boundary_common_raw_profile_eq M height (5+j) 0
    simpa only [F,Nat.add_zero,Nat.cast_zero,mul_zero,Real.rpow_zero,mul_one,add_zero] using hh
  have hK0 : 0 ≤ K := by
    have hg0 := M.shellPrefix.gamma_pos.le
    dsimp only [K]
    unfold parentBoundaryMeanKConstant parentBoundaryCommonSourceSpatialClock nativeSourceShellClock
    positivity
  have hV0 : 0 ≤ V := by
    have hg0 := M.shellPrefix.gamma_pos.le
    dsimp only [V]
    unfold parentBoundaryCommonSourceVariance nativeSourceShellClock
    positivity
  calc
    _ ≤ ∑ i : Fin height,(2*v i*R*b+2*v i*k i*R*(b*F)+v i*mu i*R^2*(b^2*F)) := by
      apply Finset.sum_le_sum
      intro i _
      exact parent_boundary_mean_protected_expectation M h hM hg q n j hqr height hheight hpast t ht i
    _ = (2*R*b)*(∑ i : Fin height,v i)+(2*R*b*F)*(∑ i : Fin height,v i*k i)+(R^2*b^2*F)*(∑ i : Fin height,v i*mu i) := by
      calc
        _ = ∑ i : Fin height,((2*R*b)*v i+(2*R*b*F)*(v i*k i)+(R^2*b^2*F)*(v i*mu i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum]
    _ ≤ (2*R*b)*V+(2*R*b*F)*K+(R^2*b^2*F)*((232/125:ℝ)*A^2) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hv (by dsimp [b,R]; positivity))
        (mul_le_mul_of_nonneg_left hk (by dsimp only [b]; positivity)))
        (mul_le_mul_of_nonneg_left hmu (by positivity))
    _ ≤ (2*E*b)*V+(2*E*b*F)*K+(E^2*b^2*F)*((232/125:ℝ)*A^2) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR.2 (by norm_num)) (by norm_num [b])) hV0
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hR.2 (by norm_num)) (by norm_num [b])) hF) hK0
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hR.1 hR.2 2) (sq_nonneg b)) hF) (by positivity)
    _ = _ := by
      rw [hFeq]
      dsimp only [parentBoundaryMeanDepthSlope,A,V,K,b,E]
      ring

end
end ASDExplicitGamma.Native
