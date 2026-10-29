module

public import ASDExplicitGamma.Native.ParentBoundaryCommonHistoryRawProfile

/-! The actual protected history drift is bounded by the literal source depth program. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The ACTUAL protected common-center history drift obeys the source
quartic/raw/center program at every depth, before summation. Every shell
and frame input is proved from the native state and structural continuity. -/
theorem parent_boundary_common_history_drift_source_depth
    (M : ABKModel 2) (h : ℝ) (P : TriadicCube 2) (n : ℤ) (r : ℕ) (hP : P.scale=n-(r:ℤ))
    (hstate : nativeInductionState M h n) (height j : ℕ) :
    parentBoundaryCommonProtectedRootDrift M h P (originCube 2 (n-((r+j:ℕ):ℤ)))
      (n-(j:ℤ)) n height (r+j) ≤ parentBoundaryCommonSourceDepthDrift M.gamma height r j := by
  obtain ⟨Q,hQ⟩ := descendantsAtDepth_nonempty P j
  have hscale : (originCube 2 (n-((r+j:ℕ):ℤ))).scale=Q.scale := by
    change n-((r+j:ℕ):ℤ)=Q.scale
    rw [scale_eq_sub_of_mem_descendantsAtDepth hQ,hP]
    omega
  rw [parent_boundary_common_protected_drift_scale_eq M h P _ Q (n-(j:ℤ)) n height (r+j) hscale]
  let R := (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-(j:ℤ)):ℝ)
  let S := (3:ℝ)^(2*M.gamma*(j:ℝ))
  let C := ∑ i : Fin height,parentBoundaryCommonProtectedShellCoefficient M h P Q (n-(j:ℤ)) n height i
  let K := parentBoundaryCommonKernelProfile (parentBoundaryCommonSourceSpatialClock M.gamma height r 2)
    (parentBoundaryCommonSourceSpatialClock M.gamma height r 4) ((1/3:ℝ)^j)
  let F := parentBoundaryBandTraceCap M height (r+j)
  let V := parentBoundaryBandVariance M h n height
  let W := parentBoundaryCommonSourceVariance M.gamma height
  let A : ℝ := (26/25:ℝ)*(3683/2500:ℝ)^2
  let B : ℝ := (26*48:ℝ)*(3683/2500:ℝ)^3
  have hA : 0 ≤ A := by norm_num [A]
  have hB : 0 ≤ B := by norm_num [B]
  have hR : 0 ≤ R ∧ R ≤ S := parent_boundary_common_protected_frame_depth M n j
  have hS : 0 ≤ S := Real.rpow_nonneg (by norm_num) _
  have hK : 0 ≤ K := parent_boundary_common_kernel_profile_nonneg _ _ _
  have hF : 0 ≤ F := parent_boundary_band_trace_cap_nonneg M height (r+j)
  have hV : 0 ≤ V := by
    unfold V parentBoundaryBandVariance
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hVW : V ≤ W := parent_boundary_band_variance_clock M h n height hstate
  have hC : C ≤ R^2*K := parent_boundary_common_protected_sum_source_kernel M h hQ (n-(j:ℤ)) n r hP hstate height
  have hR2 := pow_le_pow_left₀ hR.1 hR.2 2
  have hR3 := pow_le_pow_left₀ hR.1 hR.2 3
  have hSF : S^2*(3:ℝ)^(4*M.gamma*(j:ℝ))=(3:ℝ)^(8*M.gamma*(j:ℝ)) := by
    dsimp only [S]
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    norm_num
    ring
  have hS3 : S^3=(3:ℝ)^(6*M.gamma*(j:ℝ)) := by
    dsimp only [S]
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    congr 1
    norm_num
    ring
  have hD : parentBoundaryCommonProtectedRootDrift M h P Q (n-(j:ℤ)) n height (r+j)=C*(A*F+B*R*V) := by
    dsimp only [parentBoundaryCommonProtectedRootDrift,C,A,F,B,R,V]
    ring
  rw [hD]
  calc
    _ ≤ (R^2*K)*(A*F+B*R*V) := mul_le_mul_of_nonneg_right hC (add_nonneg (mul_nonneg hA hF) (mul_nonneg (mul_nonneg hB hR.1) hV))
    _ = K*(A*(R^2*F)+B*(R^3*V)) := by ring
    _ ≤ K*(A*(S^2*F)+B*(S^3*W)) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR2 hF) hA)
        (mul_le_mul_of_nonneg_left (mul_le_mul hR3 hVW hV (pow_nonneg hS _)) hB)) hK
    _ = _ := by
      rw [hS3]
      dsimp only [F]
      rw [parent_boundary_common_raw_profile_eq]
      have he : S^2*(parentBoundaryCommonRawFactor M.gamma height r*(3:ℝ)^(4*M.gamma*(j:ℝ))*
          (parentBoundaryCommonRawBase M.gamma height r+(32474*M.gamma)*(j:ℝ)))=
        parentBoundaryCommonRawFactor M.gamma height r*(S^2*(3:ℝ)^(4*M.gamma*(j:ℝ)))*
          (parentBoundaryCommonRawBase M.gamma height r+(32474*M.gamma)*(j:ℝ)) := by ring
      rw [he,hSF]
      dsimp only [parentBoundaryCommonSourceDepthDrift,K,A,B,W]
      ring

end
end ASDExplicitGamma.Native
