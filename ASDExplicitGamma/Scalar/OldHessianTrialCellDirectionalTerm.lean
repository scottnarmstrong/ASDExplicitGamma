module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectional
public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalTrace
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTermMoment

/-! Uniform directional depth payments before deterministic cell/load weights. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual grouped directional term on an individual fine source cell. -/
def oldHessianCellDirectionalTerm (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (e : Vec 2) (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1-inverseHistoryDiscount^2)*inverseHistoryDiscount^(2*j)*
    ((3683/2500:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω)*
      oldHessianCellDepthDirectional M m U j e ω

/-- Each cell and deterministic load has the same genuine half-trace
leading payment and correlated full-trace local rare payment. -/
theorem old_hessian_cell_directional_term_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134)
    (e : Vec 2) (j : ℕ) :
    Integrable (oldHessianCellDirectionalTerm M m U e j) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianCellDirectionalTerm M m U e j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (mixedBridgeLocalWeight M j/2*inSourceMeanActual M m (5+j) 0+
          oldHessianWeakRareBudget M 0 j)*vecNormSq e := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := oldHessianLocalDepthRare M m j
  let D := oldHessianCellDepthDirectional M m U j e
  let T := oldHessianCellDepthTrace M m U j
  let w := (1-inverseHistoryDiscount^2)*inverseHistoryDiscount^(2*j)
  let b := (3683/2500:ℝ)*bankDepthFrame M j
  have hscale : U.scale=m-5 := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale=m+129-134 at hs
    omega
  have hw : 0≤w := mul_nonneg (sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le))
    (pow_nonneg inverse_history_discount_range.1.le _)
  have hb : 0≤b := mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le
  have hD := old_hessian_cell_directional_mean M m U hU j e
  have hT := old_hessian_cell_depth_trace_mean M m U hscale j
  have hR := old_hessian_actual_local_depth_rare M h hM hg N hpast m hm j
  have hε : 0≤5*inverseBankDepthReserve .localInverse M j := by
    unfold inverseBankDepthReserve
    have hr : 0≤(inverseBankReserve .localInverse:ℝ) := by norm_num [inverseBankReserve]
    have hf := (bankDepthFrame_pos M j).le
    positivity
  have hr := old_signed_rare_directional_integrable_bound R T D
    (5*inverseBankDepthReserve .localInverse M j) (rawWeakTraceProfileEnvelope M j) (vecNormSq e)
    1 (by norm_num) hε (old_hessian_raw_profile_nonneg M j) (vecNormSq_nonneg e)
    hR.2.1 (fun ω => raw_weak_trace_sequence_nonneg M m U 0 (by norm_num) ω j)
    (fun ω => (old_hessian_cell_directional_bounds M m U hU j e ω).1)
    (fun ω => (old_hessian_cell_directional_bounds M m U hU j e ω).2)
    hR.1.aestronglyMeasurable hT.1.aestronglyMeasurable hD.1.aestronglyMeasurable hR.2.2
    (old_hessian_cell_depth_trace_profile M h hM hg N hpast m hm U hscale j)
  simp only [pow_one] at hr
  have hexpand : oldHessianCellDirectionalTerm M m U e j=
      (fun ω => (w*b)*D ω+w*(R ω*D ω)) := by
    funext ω
    unfold oldHessianCellDirectionalTerm
    dsimp only [w,b,R,D]
    ring
  have hi : Integrable (fun ω => (w*b)*D ω+w*(R ω*D ω)) μ :=
    (hD.1.const_mul (w*b)).add (hr.1.const_mul w)
  refine ⟨hexpand.symm ▸ hi,?_⟩
  rw [hexpand,integral_add (hD.1.const_mul (w*b)) (hr.1.const_mul w),integral_const_mul,integral_const_mul]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hD.2.le (mul_nonneg hw hb))
    (mul_le_mul_of_nonneg_left hr.2 hw)
  apply hh.trans_eq
  norm_num [oldHessianWeakRareBudget,rareExpansionTail]
  unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
  dsimp only [w,b,bankDepthFrame]
  ring

end
end ASDExplicitGamma.Scalar
