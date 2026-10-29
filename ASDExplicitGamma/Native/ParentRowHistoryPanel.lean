module

public import ASDExplicitGamma.Native.ParentRowHistoryDeltaBridge
public import ASDExplicitGamma.Native.ParentRowHistoryInitialFields
public import ASDExplicitGamma.Native.ParentRowFlatPayment
public import ASDExplicitGamma.Native.ParentHistoryEndpoint

/-! The actual physical history envelope is the exact stored parent panel history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Cold Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- Every selected history drift is the actual closed source drift at mesh five. -/
theorem parent_row_history_delta_field (j : Fin 16) :
    (parentRowFields j).getD 10 0=parentBoundaryCommonSourceDelta gammaZero (j.val+1) 5 := by
  rw [parent_row_history_delta_eq]
  fin_cases j <;> simp only [parentRowFields,nativeConfiguredParentEndpoint,
    nativeParentEndpointCertificates,nativeParent001EndpointCertificate,nativeParent002EndpointCertificate,nativeParent003EndpointCertificate,nativeParent004EndpointCertificate,nativeParent005EndpointCertificate,nativeParent006EndpointCertificate,nativeParent007EndpointCertificate,nativeParent008EndpointCertificate,nativeParent009EndpointCertificate,nativeParent010EndpointCertificate,nativeParent011EndpointCertificate,nativeParent012EndpointCertificate,nativeParent013EndpointCertificate,nativeParent014EndpointCertificate,nativeParent015EndpointCertificate,nativeParent016EndpointCertificate,
    List.getD_cons_zero,List.getD_cons_succ]
  · exact parent_row_delta_expr_001.trans (parent_row_history_delta_expr_eval _ (by rfl) 1)
  · exact parent_row_delta_expr_002.trans (parent_row_history_delta_expr_eval _ (by rfl) 2)
  · exact parent_row_delta_expr_003.trans (parent_row_history_delta_expr_eval _ (by rfl) 3)
  · exact parent_row_delta_expr_004.trans (parent_row_history_delta_expr_eval _ (by rfl) 4)
  · exact parent_row_delta_expr_005.trans (parent_row_history_delta_expr_eval _ (by rfl) 5)
  · exact parent_row_delta_expr_006.trans (parent_row_history_delta_expr_eval _ (by rfl) 6)
  · exact parent_row_delta_expr_007.trans (parent_row_history_delta_expr_eval _ (by rfl) 7)
  · exact parent_row_delta_expr_008.trans (parent_row_history_delta_expr_eval _ (by rfl) 8)
  · exact parent_row_delta_expr_009.trans (parent_row_history_delta_expr_eval _ (by rfl) 9)
  · exact parent_row_delta_expr_010.trans (parent_row_history_delta_expr_eval _ (by rfl) 10)
  · exact parent_row_delta_expr_011.trans (parent_row_history_delta_expr_eval _ (by rfl) 11)
  · exact parent_row_delta_expr_012.trans (parent_row_history_delta_expr_eval _ (by rfl) 12)
  · exact parent_row_delta_expr_013.trans (parent_row_history_delta_expr_eval _ (by rfl) 13)
  · exact parent_row_delta_expr_014.trans (parent_row_history_delta_expr_eval _ (by rfl) 14)
  · exact parent_row_delta_expr_015.trans (parent_row_history_delta_expr_eval _ (by rfl) 15)
  · exact parent_row_delta_expr_016.trans (parent_row_history_delta_expr_eval _ (by rfl) 16)

/-- The history subexpression used literally by the certified parent panel. -/
def parentRowPanelHistory (j : Fin 16) (t : ℝ) : ℝ :=
  let f := fun i => (parentRowFields j).getD i 0
  (Real.sqrt (f 13+f 10*t)+Real.sqrt (2*f 0*t)*
    (Real.sqrt (Real.sqrt 3)*Real.sqrt (3683/2500:ℝ)+
      Real.sqrt (Real.sqrt (Real.sqrt 105))*Real.sqrt (3/10^46:ℝ)))^2

/-- Exact physical-to-panel history identification; no rounded cap or
coefficient estimate is inserted. -/
theorem parent_row_history_panel_eq (j : Fin 16) (t : ℝ) :
    parentHistorySourceEnvelope (j.val+1) 5 t=parentRowPanelHistory j t := by
  have hquarter (x : ℝ) (hx : 0≤x) : Real.sqrt (Real.sqrt x)=x^(1/4:ℝ) := by
    simp only [Real.sqrt_eq_rpow]
    rw [←Real.rpow_mul hx]
    norm_num
  have heighth (x : ℝ) (hx : 0≤x) : Real.sqrt (Real.sqrt (Real.sqrt x))=x^(1/8:ℝ) := by
    rw [hquarter x hx,Real.sqrt_eq_rpow,←Real.rpow_mul hx]
    norm_num
  unfold parentHistorySourceEnvelope parentRowPanelHistory
  dsimp only
  rw [parent_row_h0_field,parent_row_history_delta_field,parent_row_variance_eq,
    parent_row_mean_variance_eq,hquarter 3 (by norm_num),heighth 105 (by norm_num)]
  norm_num only [Nat.cast_ofNat,show (3:ℝ)*5/20=3/4 by norm_num]
  congr 3 <;> ring

end
end ASDExplicitGamma.Native
