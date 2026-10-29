module

public import ASDExplicitGamma.Native.ParentRowA2Fields
public import ASDExplicitGamma.Native.ParentRowYFields

/-! Selected exact derivative and Dirichlet clocks for the sixteen parent rows. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The selected A2 field is its exact weighted physical shell clock. -/
theorem parent_row_a2_eq (j : Fin 16) :
    (parentRowFields j).getD 1 0=
      parentRowWeightedClock parentRowA2Weight (j.val+1) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_a2_001
  · exact parent_row_a2_002
  · exact parent_row_a2_003
  · exact parent_row_a2_004
  · exact parent_row_a2_005
  · exact parent_row_a2_006
  · exact parent_row_a2_007
  · exact parent_row_a2_008
  · exact parent_row_a2_009
  · exact parent_row_a2_010
  · exact parent_row_a2_011
  · exact parent_row_a2_012
  · exact parent_row_a2_013
  · exact parent_row_a2_014
  · exact parent_row_a2_015
  · exact parent_row_a2_016

/-- The actual weighted shell variance fits the selected A2 field with one theta factor. -/
theorem parent_row_actual_a2_weighted_variance
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    (∑ i : Fin (j.val+1),
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2*
        (parentRowA2Weight i.val:ℝ))≤theta M*(parentRowFields j).getD 1 0 := by
  rw [parent_row_a2_eq]
  exact parent_row_weighted_actual_variance M h hg n (j.val+1) hstate
    parentRowA2Weight (fun k => by unfold parentRowA2Weight; positivity)

/-- The selected Y field is its exact weighted physical shell clock. -/
theorem parent_row_y_eq (j : Fin 16) :
    (parentRowFields j).getD 16 0=
      parentRowWeightedClock parentRowYWeight (j.val+1) := by
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate, nativeParent002EndpointCertificate, nativeParent003EndpointCertificate, nativeParent004EndpointCertificate, nativeParent005EndpointCertificate, nativeParent006EndpointCertificate, nativeParent007EndpointCertificate, nativeParent008EndpointCertificate, nativeParent009EndpointCertificate, nativeParent010EndpointCertificate, nativeParent011EndpointCertificate, nativeParent012EndpointCertificate, nativeParent013EndpointCertificate, nativeParent014EndpointCertificate, nativeParent015EndpointCertificate, nativeParent016EndpointCertificate,List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_y_001
  · exact parent_row_y_002
  · exact parent_row_y_003
  · exact parent_row_y_004
  · exact parent_row_y_005
  · exact parent_row_y_006
  · exact parent_row_y_007
  · exact parent_row_y_008
  · exact parent_row_y_009
  · exact parent_row_y_010
  · exact parent_row_y_011
  · exact parent_row_y_012
  · exact parent_row_y_013
  · exact parent_row_y_014
  · exact parent_row_y_015
  · exact parent_row_y_016

/-- The actual weighted shell variance fits the selected Y field with one theta factor. -/
theorem parent_row_actual_y_weighted_variance
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    (∑ i : Fin (j.val+1),
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2*
        (parentRowYWeight i.val:ℝ))≤theta M*(parentRowFields j).getD 16 0 := by
  rw [parent_row_y_eq]
  exact parent_row_weighted_actual_variance M h hg n (j.val+1) hstate
    parentRowYWeight (fun k => by unfold parentRowYWeight; positivity)

end
end ASDExplicitGamma.Native
