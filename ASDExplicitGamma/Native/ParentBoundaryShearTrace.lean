module

public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw

/-! Exact restoration of the physical scalar center after remainder heat. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- Adding a scalar center obeys the exact trace quadratic, in the SAME
response frame. The coefficient is an arbitrary actual continuous field. -/
theorem parent_boundary_model_trace_add_constant
    (q : ℤ) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet (originCube 2 q)),ℝ)) (g : ℝ) :
    let A := coarseBlockMatrix (cubeSet (originCube 2 q)) (responsePlanarCoefficientField ν
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ f))
    modelTraceObservable q ν σ (f+ContinuousMap.const _ g)=modelTraceObservable q ν σ f+
      2*(g/σ)*shearTraceLinear A+(g/σ)^2*bankInverseTraceObservable q ν σ hν hσ f := by
  intro A
  let Q := originCube 2 q
  let U := cubeSet Q
  let K := closure U
  let L := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ
  let k := L f
  have hL : L (f+ContinuousMap.const K g)=k+BoundedContinuousFunction.const K g := by
    ext x
    simp [L,k]
  have hcoeff (x : Vec 2) (hx : x∈U) :
      responseCoefficientExtension (L (f+ContinuousMap.const K g)) x=responseCoefficientExtension k x+g := by
    rw [hL,responseCoefficientExtension_add_on k (BoundedContinuousFunction.const K g) hx,
      responseCoefficientExtension_eq (BoundedContinuousFunction.const K g) hx]
    rfl
  have hae : responsePlanarCoefficientField ν (L (f+ContinuousMap.const K g))=ᵐ[volume.restrict U]
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x+g)) := by
    filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_cubeSet Q)] with x hx
    simp only [responsePlanarCoefficientField,hcoeff x hx]
  have he := nativeTraceDefect_constantShear ν σ hν hσ (responseCoefficientExtension k)
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k) g
  have hd : bankInverseTraceObservable q ν σ hν hσ f=Matrix.trace (frameMatrix σ A).lowerRight := by
    rw [bank_inverse_trace_observable_eq]
    simp [A,bankInverseTrace,frameMatrix,Matrix.trace,Fin.sum_univ_two,
      Matrix.diag_apply,Matrix.smul_apply,smul_eq_mul]
  have ht : modelTraceObservable q ν σ (f+ContinuousMap.const K g)=
      traceDefect U (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x+g)) σ := by
    unfold modelTraceObservable traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hae]
  rw [ht,he,hd]
  change traceDefect U (responsePlanarCoefficientField ν k) σ+2*(g/σ)*shearTraceLinear A+
    g^2*(Matrix.trace (frameMatrix σ A).lowerRight/σ^2)=_
  dsimp [modelTraceObservable,traceDefect,A,Q,U,K,L,k]
  ring

/-- The honest square-root trace triangle for a physical constant shear.
No response, inverse, or signed linear bound is assumed. -/
theorem parent_boundary_model_trace_shear_upper
    (q : ℤ) (ν σ : ℝ) (hν : 0<ν) (hσ : 0<σ)
    (f : C(closure (cubeSet (originCube 2 q)),ℝ)) (g : ℝ) :
    modelTraceObservable q ν σ (f+ContinuousMap.const _ g)≤
      (Real.sqrt (modelTraceObservable q ν σ f)+|g/σ| *
        Real.sqrt (bankInverseTraceObservable q ν σ hν hσ f))^2 := by
  let A := coarseBlockMatrix (cubeSet (originCube 2 q)) (responsePlanarCoefficientField ν
    (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ f))
  let T := modelTraceObservable q ν σ f
  let D := bankInverseTraceObservable q ν σ hν hσ f
  let z := shearTraceLinear A
  have hT : 0≤T := modelTraceObservable_nonneg q ν σ hν hσ f
  have hd : D=Matrix.trace (frameMatrix σ A).lowerRight := by
    dsimp only [D]
    rw [bank_inverse_trace_observable_eq]
    simp [A,bankInverseTrace,frameMatrix,Matrix.trace,Fin.sum_univ_two,
      Matrix.diag_apply,Matrix.smul_apply,smul_eq_mul]
  have hD : 0≤D := by
    have hh := (nativeTraceShearDefectRows (originCube 2 q) ν σ hν hσ
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ f)).2.1
    change 0<Matrix.trace (frameMatrix σ A).lowerRight/σ^2 at hh
    have hp := mul_nonneg hh.le (sq_nonneg σ)
    rw [div_mul_cancel₀ _ (sq_pos_of_pos hσ).ne'] at hp
    rw [hd]
    exact hp
  have hz : z^2≤D*T := by
    rw [hd]
    exact shearTraceLinear_sq_le (originCube 2 q) ν σ hν hσ _
  have hzabs : |z|≤Real.sqrt T*Real.sqrt D := by
    have hs : (Real.sqrt T*Real.sqrt D)^2=T*D := by
      rw [mul_pow,Real.sq_sqrt hT,Real.sq_sqrt hD]
    have hn : 0≤Real.sqrt T*Real.sqrt D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith only [hz,hs,sq_abs z,abs_nonneg z,hn]
  have hlin : (g/σ)*z≤|g/σ| *(Real.sqrt T*Real.sqrt D) :=
    (le_abs_self ((g/σ)*z)).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hzabs (abs_nonneg _))
  rw [parent_boundary_model_trace_add_constant q ν σ hν hσ f g]
  change T+2*(g/σ)*z+(g/σ)^2*D≤(Real.sqrt T+|g/σ| *Real.sqrt D)^2
  nlinarith only [hlin,Real.sq_sqrt hT,Real.sq_sqrt hD,sq_abs (g/σ)]

end
end ASDExplicitGamma.Native
