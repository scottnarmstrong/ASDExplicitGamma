module

public import ASDExplicitGamma.Response.Analytic

/-! Exact finite-load differentiation of the actual response trace.
Only source C2 regularity is used; no Hessian estimate is a premise. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Differentiate a finite actual response sum with its constant trace
defect subtraction; the coefficient direction is retained exactly. -/
theorem old_signed_fderiv_sum_sub_const {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (f : I → E → ℝ) (hf : ∀ i,ContDiff ℝ 2 (f i)) (c : ℝ) (x H : E) :
    fderiv ℝ (fun y => (∑ i,f i y)-c) x H=∑ i,fderiv ℝ (f i) x H := by
  have hD (i : I) : DifferentiableAt ℝ (f i) x :=
    ((hf i).differentiable (by norm_num)).differentiableAt
  have hd := (HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (hD i).hasFDerivAt)).sub_const c
  have hsum : (∑ i,f i)=(fun y => ∑ i,f i y) := by
    funext y
    simp only [Finset.sum_apply]
  rw [hsum] at hd
  have he := congrArg (fun L : E →L[ℝ] ℝ => L H) hd.fderiv
  simpa only [sum_apply] using he

/-- The complete finite-load second derivative identity for the same
physical coefficient direction and source constant subtraction. -/
theorem old_signed_second_fderiv_sum_sub_const {E I : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (f : I → E → ℝ) (hf : ∀ i,ContDiff ℝ 2 (f i)) (c : ℝ) (x H : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => (∑ i,f i y)-c) z H) x H=
      ∑ i,fderiv ℝ (fun z => fderiv ℝ (f i) z H) x H := by
  have he : (fun z => fderiv ℝ (fun y => (∑ i,f i y)-c) z H)=
      fun z => ∑ i,fderiv ℝ (f i) z H :=
    funext (fun z => old_signed_fderiv_sum_sub_const f hf c z H)
  rw [he]
  have hd (i : I) : DifferentiableAt ℝ (fun z => fderiv ℝ (f i) z H) x :=
    (((hf i).fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1≤2)).clm_apply
      contDiff_const).differentiable_one.differentiableAt
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L H)
    (HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => (hd i).hasFDerivAt)).fderiv
  have hsum : (∑ i,fun z => fderiv ℝ (f i) z H)=(fun z => ∑ i,fderiv ℝ (f i) z H) := by
    funext z
    simp only [Finset.sum_apply]
  rw [hsum] at hh
  simpa only [sum_apply] using hh

end
end ASDExplicitGamma.Native
