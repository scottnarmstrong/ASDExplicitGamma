module

public import ASDExplicitGamma.Native.OldSignedQ1InputControl
public import ASDExplicitGamma.Native.OldSignedQ1PaymentAlgebra
public import ASDExplicitGamma.Numerics.Native.PanelReadable

/-! Identification with the unchanged, certified OLD q1 panel program. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Scalar Inverse Algsuperdiff.Section3 Numerics.Native Numerics.Mirror
noncomputable section

private theorem q1_sqrt_quarter (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x)=x^(1/4:ℝ) := by
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul hx]
  norm_num

private theorem q1_sqrt_eighth (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt (Real.sqrt x))=x^(1/8:ℝ) := by
  rw [q1_sqrt_quarter x hx,Real.sqrt_eq_rpow,←Real.rpow_mul hx]
  norm_num

/-- The endpoint input vector has exactly the collected panel parameters. -/
theorem old_signed_q1_endpoint_abstract (t : ℝ) :
    oldSignedQ1PaymentEndpoint t=oldSignedQ1AbstractEndpoint
      (nativeSetupQ1001FieldsR.getD 0 0) (nativeSetupQ1001FieldsR.getD 1 0)
      (nativeSetupQ1001FieldsR.getD 2 0) (nativeSetupQ1001FieldsR.getD 3 0)
      (nativeSetupQ1001FieldsR.getD 4 0) (nativeSetupQ1001FieldsR.getD 5 0)
      (nativeSetupQ1001FieldsR.getD 6 0) (oldSignedQ1PanelXi t)
      ((1+inverseHistoryDiscount)*oldSignedQ1PanelMatrix t*oldSignedQ1PanelHistory t)
      (oldSignedQ1PanelMatrix t) (1+inverseHistoryDiscount)
      (Real.sqrt ((3683/2500:ℝ)*oldSignedQ1PanelMatrix t)+1) (oldSignedQ1PanelMean t) := rfl

/-- The readable numerical panel and the collected complete bill agree. -/
theorem old_signed_q1_collected_panel (t : ℝ) :
    oldSignedQ1CollectedBill
      (nativeSetupQ1001FieldsR.getD 0 0) (nativeSetupQ1001FieldsR.getD 1 0)
      (nativeSetupQ1001FieldsR.getD 2 0) (nativeSetupQ1001FieldsR.getD 3 0)
      (nativeSetupQ1001FieldsR.getD 4 0) (nativeSetupQ1001FieldsR.getD 5 0)
      (nativeSetupQ1001FieldsR.getD 6 0) (oldSignedQ1PanelXi t)
      ((1+inverseHistoryDiscount)*oldSignedQ1PanelMatrix t*oldSignedQ1PanelHistory t)
      (oldSignedQ1PanelMatrix t) (1+inverseHistoryDiscount)
      (Real.sqrt ((3683/2500:ℝ)*oldSignedQ1PanelMatrix t)+1) (oldSignedQ1PanelMean t)=
      nativePanelValue nativeSetupQ1001FieldsR t := by
  let f := fun i => nativeSetupQ1001FieldsR.getD i 0
  have hfields : nativeSetupQ1001FieldsR=
      [f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7,f 8,f 9,f 10,f 11,f 12,f 13,f 14,f 15,f 16] := by
    simp only [f,nativeSetupQ1001FieldsR,List.getD_cons_zero,List.getD_cons_succ]
  conv_rhs => rw [hfields,nativePanelValue_readable]
  have hx : f 8=Real.sqrt (2*f 0) := by
    rw [show f 8=nativeSetupQ1001FieldsR.getD 8 0 from rfl,old_signed_q1_setup_readable_08]
    congr 1
    ring
  have hy : f 9=Real.sqrt (f 0) := old_signed_q1_setup_readable_09
  have hb : f 7=f 6 := old_signed_q1_setup_boundary_same
  have hv : f 16=f 0 := old_signed_q1_setup_ybar
  have hH : (Real.sqrt (f 13+f 10*t)+Real.sqrt (2*f 0*t)*
      (Real.sqrt (Real.sqrt 3)*Real.sqrt (3683/2500:ℝ)+
        Real.sqrt (Real.sqrt (Real.sqrt 105))*Real.sqrt (3/10^46:ℝ)))^2=oldSignedQ1PanelHistory t := by
    rw [q1_sqrt_quarter 3 (by norm_num),q1_sqrt_eighth 105 (by norm_num)]
    rfl
  have hD : 1+1/Real.sqrt (Real.sqrt 3)=1+inverseHistoryDiscount := by
    rw [q1_sqrt_quarter 3 (by norm_num),one_div,inverse_history_discount_eq]
  have ha : f 14+f 11*t=oldSignedQ1PanelMean t := by unfold oldSignedQ1PanelMean; ring
  have hX : f 15+f 12*t=oldSignedQ1PanelXi t := by unfold oldSignedQ1PanelXi; ring
  have hA : 0 ≤ oldSignedQ1PanelMatrix t := add_nonneg
    (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  dsimp only [nativeOldBoundaryPanel]
  rw [hx,hy,hb,hv,hH,hD,ha,hX]
  dsimp only [oldSignedQ1PanelMatrix] at hA
  rw [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 3683/2500) hA)]
  rfl

/-- Exact endpoint bill identification, without any estimate premise. -/
theorem old_signed_q1_payment_endpoint_eq_panel (t : ℝ) (ht : 0 ≤ t) :
    evalReal (oldSignedQ1PaymentEndpoint t) oldSignedQ1PaymentExpr=
      nativePanelValue nativeSetupQ1001FieldsR t := by
  rw [old_signed_q1_endpoint_abstract]
  have hX : 0 ≤ oldSignedQ1PanelXi t := add_nonneg
    (old_signed_q1_setup_field_nonneg ⟨15,by omega⟩)
    (mul_nonneg ht (old_signed_q1_setup_field_nonneg ⟨12,by omega⟩))
  have hA : 0 ≤ oldSignedQ1PanelMatrix t := add_nonneg
    (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg _))) (Real.sqrt_nonneg _)
  have hY : 0 ≤ (1+inverseHistoryDiscount)*oldSignedQ1PanelMatrix t*oldSignedQ1PanelHistory t :=
    mul_nonneg (mul_nonneg (add_nonneg (by norm_num) inverse_history_discount_range.1.le) hA)
      (sq_nonneg _)
  rw [old_signed_q1_payment_algebra _ _ _ _ _ _ _ _ _ _ _ _ _
    old_signed_q1_setup_variance_nonneg (old_signed_q1_setup_field_nonneg ⟨4,by omega⟩)
    (old_signed_q1_setup_field_nonneg ⟨5,by omega⟩) hX hY]
  exact old_signed_q1_collected_panel t

/-- The actual full affine and AN error bill is paid by the certified panel. -/
theorem old_signed_q1_payment_panel_bound
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (t : ℝ) (ht : 0 ≤ t) :
    let b := q3ModelAmplitude M h (n+1)/(Annealed.sigmaBar M n:ℝ)
    let L := q3ModelLength (n+1)
    oldSignedQ1AffineCap M n t b L+oldSignedQ1ErrorCap M n t b L ≤
      theta M*nativePanelValue nativeSetupQ1001FieldsR t := by
  rw [←old_signed_q1_payment_endpoint_eq_panel t ht]
  exact old_signed_q1_payment_endpoint_bound M h hg n hstate t ht

end
end ASDExplicitGamma.Native
