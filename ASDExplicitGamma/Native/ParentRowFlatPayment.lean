module

public import ASDExplicitGamma.Native.ParentRowVariances
public import ASDExplicitGamma.Native.ParentRowBaselines

/-! Actual full parent variance and flat payment in the exact source setups. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The selected variance is the exact finite physical endpoint shell sum. -/
theorem parent_row_variance_eq (j : Fin 16) :
    (parentRowFields j).getD 0 0=parentRowVarianceClock (j.val+1) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_variance_001
  · exact parent_row_variance_002
  · exact parent_row_variance_003
  · exact parent_row_variance_004
  · exact parent_row_variance_005
  · exact parent_row_variance_006
  · exact parent_row_variance_007
  · exact parent_row_variance_008
  · exact parent_row_variance_009
  · exact parent_row_variance_010
  · exact parent_row_variance_011
  · exact parent_row_variance_012
  · exact parent_row_variance_013
  · exact parent_row_variance_014
  · exact parent_row_variance_015
  · exact parent_row_variance_016


/-- The selected flat allocation is twice the same full variance. -/
theorem parent_row_baseline_eq (j : Fin 16) :
    parentRowB0 j=2*(parentRowFields j).getD 0 0 := by
  fin_cases j <;> simp only [parentRowB0,parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_baseline_001
  · exact parent_row_baseline_002
  · exact parent_row_baseline_003
  · exact parent_row_baseline_004
  · exact parent_row_baseline_005
  · exact parent_row_baseline_006
  · exact parent_row_baseline_007
  · exact parent_row_baseline_008
  · exact parent_row_baseline_009
  · exact parent_row_baseline_010
  · exact parent_row_baseline_011
  · exact parent_row_baseline_012
  · exact parent_row_baseline_013
  · exact parent_row_baseline_014
  · exact parent_row_baseline_015
  · exact parent_row_baseline_016


/-- Physical full variance is paid with its single theta factor at every row. -/
theorem parent_row_actual_variance
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    parentBoundaryBandVariance M h n (j.val+1)≤theta M*(parentRowFields j).getD 0 0 := by
  rw [parent_row_variance_eq]
  exact parent_row_actual_variance_clock M h hg n (j.val+1) hstate

/-- The complete physical flat baseline fits the stored source allocation.
The signed inverse-deficit contribution is not charged here a second time. -/
theorem parent_row_actual_flat_payment
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    (∑ i : Fin (j.val+1),oldSignedFlatBoundaryEnergy (originCube 2 n)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))))≤theta M*parentRowB0 j := by
  rw [parent_boundary_band_flat_baseline]
  have hy := (parent_boundary_band_energy_bounds M h n (j.val+1)).1
  apply (sub_le_self _ (mul_nonneg (by norm_num : (0:ℝ)≤2) hy)).trans
  have hv := mul_le_mul_of_nonneg_left
    (parent_row_actual_variance M h hg n hstate j) (by norm_num : (0:ℝ)≤2)
  rw [parent_row_baseline_eq]
  convert hv using 1
  ring

end
end ASDExplicitGamma.Native
