module

public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryDriftBound

/-! The complete actual centered-history drift is bounded by the exact finite source delta program. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Literal source delta, with all five geometric degrees summed exactly.
The first branch pays the physical full response; the second pays the48v
shared-center product on the original cutoff law. -/
def parentBoundaryCommonSourceDelta (gamma : ℝ) (height r : ℕ) : ℝ :=
  (1-inverseHistoryDiscount)*
    ((26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryCommonRawFactor gamma height r*
      parentBoundaryCommonKernelGeometric
        (parentBoundaryCommonSourceSpatialClock gamma height r 2)
        (parentBoundaryCommonSourceSpatialClock gamma height r 4) gamma 8
        (parentBoundaryCommonRawBase gamma height r) (32474*gamma)+
      (26*48:ℝ)*parentBoundaryCommonSourceVariance gamma height*(3683/2500:ℝ)^3*
        parentBoundaryCommonKernelGeometric
          (parentBoundaryCommonSourceSpatialClock gamma height r 2)
          (parentBoundaryCommonSourceSpatialClock gamma height r 4) gamma 6 1 0)

/-- The literal source depth program is summable and its complete sum is
exactly the source delta, including the normalized history weight. -/
theorem parent_boundary_common_source_delta_sum
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (height r : ℕ) :
    Summable (fun j : ℕ => coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift gamma height r j) ∧
      (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift gamma height r j)=
        parentBoundaryCommonSourceDelta gamma height r := by
  let A2 := parentBoundaryCommonSourceSpatialClock gamma height r 2
  let A4 := parentBoundaryCommonSourceSpatialClock gamma height r 4
  let U := parentBoundaryCommonRawBase gamma height r
  let V := 32474*gamma
  let C := (26/25:ℝ)*(3683/2500:ℝ)^2*parentBoundaryCommonRawFactor gamma height r
  let D := (26*48:ℝ)*parentBoundaryCommonSourceVariance gamma height*(3683/2500:ℝ)^3
  let F := fun (growth : ℝ) (a b : ℝ) (j : ℕ) => coldHistoryBeta^j*
    parentBoundaryCommonKernelProfile A2 A4 ((1/3:ℝ)^j)*(3:ℝ)^(growth*gamma*(j:ℝ))*(a+b*(j:ℝ))
  have h8 := parent_boundary_common_kernel_geometric_sum A2 A4 gamma 8 U V hg0 hg (by norm_num)
  have h6 := parent_boundary_common_kernel_geometric_sum A2 A4 gamma 6 1 0 hg0 hg (by norm_num)
  have he : (fun j : ℕ => coldHistoryBeta^j*parentBoundaryCommonSourceDepthDrift gamma height r j)=
      (fun j : ℕ => C*F 8 U V j+D*F 6 1 0 j) := by
    funext j
    dsimp only [parentBoundaryCommonSourceDepthDrift,C,D,F,A2,A4,U,V]
    ring
  rw [he]
  refine ⟨(h8.1.mul_left C).add (h6.1.mul_left D),?_⟩
  rw [(h8.1.mul_left C).tsum_add (h6.1.mul_left D),tsum_mul_left,tsum_mul_left,h8.2,h6.2]
  rfl

/-- The exact finite source delta is nonnegative on the entire gamma range. -/
theorem parent_boundary_common_source_delta_nonneg
    (gamma : ℝ) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (height r : ℕ) :
    0 ≤ parentBoundaryCommonSourceDelta gamma height r := by
  rw [←(parent_boundary_common_source_delta_sum gamma hg0 hg height r).2]
  exact mul_nonneg (sub_nonneg.mpr inverse_history_discount_range.2.le)
    (tsum_nonneg (fun j => mul_nonneg (pow_nonneg coldHistoryBeta_pos.le _)
      (parent_boundary_common_source_depth_drift_nonneg hg0 height r j)))

/-- The ACTUAL complete protected-frame history drift is finite and bounded
by the source delta. No geometric or moment estimate is a premise. -/
theorem parent_boundary_common_actual_history_drift_le_delta
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (P : TriadicCube 2) (n : ℤ)
    (r : ℕ) (hP : P.scale=n-(r:ℤ)) (hstate : nativeInductionState M h n) (height : ℕ) :
    parentBoundaryCommonProtectedHistoryDrift M h P n height r ≤
      ENNReal.ofReal (parentBoundaryCommonSourceDelta M.gamma height r) := by
  let D := fun j : ℕ => parentBoundaryCommonProtectedRootDrift M h P
    (originCube 2 (n-((r+j:ℕ):ℤ))) (n-(j:ℤ)) n height (r+j)
  let G := parentBoundaryCommonSourceDepthDrift M.gamma height r
  have hD0 (j) : 0 ≤ coldHistoryBeta^j*D j := mul_nonneg (pow_nonneg coldHistoryBeta_pos.le _)
    (parent_boundary_common_protected_root_drift_nonneg M h P _ _ _ _ _)
  have hle (j) : coldHistoryBeta^j*D j ≤ coldHistoryBeta^j*G j :=
    mul_le_mul_of_nonneg_left (parent_boundary_common_history_drift_source_depth M h P n r hP hstate height j)
      (pow_nonneg coldHistoryBeta_pos.le _)
  have hG := parent_boundary_common_source_delta_sum M.gamma M.shellPrefix.gamma_pos.le hg height r
  have hsumD : Summable (fun j : ℕ => coldHistoryBeta^j*D j) := Summable.of_nonneg_of_le hD0 hle hG.1
  change ENNReal.ofReal (1-inverseHistoryDiscount)*(∑' j : ℕ,ENNReal.ofReal (coldHistoryBeta^j*D j)) ≤ _
  rw [←ENNReal.ofReal_tsum_of_nonneg hD0 hsumD,
    ←ENNReal.ofReal_mul (sub_nonneg.mpr inverse_history_discount_range.2.le)]
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (hsumD.tsum_le_tsum hle hG.1)
    (sub_nonneg.mpr inverse_history_discount_range.2.le)).trans_eq hG.2

/-- Sharp centered history envelope on the ACTUAL cutoff law.
The native initial strong coefficient, theta factor and exact source delta
are retained, with every infinitely deep descendant already paid. -/
theorem parent_boundary_common_centered_history_delta_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (parentBoundaryCommonCenteredMaxHistory M P n height t) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((coldHistoryBeta^r)⁻¹*((2379/2500:ℝ)*theta M)+
        t*parentBoundaryCommonSourceDelta M.gamma height r) := by
  have hh := parent_boundary_common_protected_history_transport M h hM hg P n r hr hP hstate height hheight hpast t ht0 ht1
  have hd := parent_boundary_common_actual_history_drift_le_delta M h hg P n r hP hstate height
  have hstart : 0 ≤ (coldHistoryBeta^r)⁻¹*((2379/2500:ℝ)*theta M) :=
    mul_nonneg (inv_nonneg.mpr (pow_nonneg coldHistoryBeta_pos.le _))
      (mul_nonneg (by norm_num) (cold_theta_pos M).le)
  have hdelta := parent_boundary_common_source_delta_nonneg M.gamma M.shellPrefix.gamma_pos.le hg height r
  apply (hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (by positivity)))).trans_eq
  rw [←ENNReal.ofReal_mul ht0,←ENNReal.ofReal_add hstart (mul_nonneg ht0 hdelta)]

end
end ASDExplicitGamma.Native
