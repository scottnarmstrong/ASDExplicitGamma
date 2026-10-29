module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectionalTerm
public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalTrace
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaTermMoment
public import ASDExplicitGamma.Scalar.OldHessianTrialDirectionalRare
public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedSource

/-! Uniform fine-cell directional half bounds for arbitrary deterministic loads. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Complete grouped directional proxy on one actual source cell. -/
def oldHessianCellDirectionalTheta (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) : ℝ := ∑' j,oldHessianCellDirectionalTerm M m U e j ω

/-- Every fine cell and deterministic load has a convergent, integrable
proxy with the same uniform Xi/2 times squared-load payment. -/
theorem old_hessian_actual_cell_directional_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) (e : Vec 2) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j => oldHessianCellDirectionalTerm M m U e j ω)) ∧
    Integrable (oldHessianCellDirectionalTheta M m U e) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianCellDirectionalTheta M m U e ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerXiExpr/2*vecNormSq e := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := oldHessianCellDirectionalTerm M m U e
  let S := fun j : ℕ => mixedBridgeLocalWeight M j*inSourceMeanActual M m (5+j) 0
  let C := fun j : ℕ => (1/2:ℝ)*S j+oldHessianWeakRareBudget M 0 j
  have hsource := mixed_bridge_local_mean_transport M h hM hg N hpast m hm 0 (by norm_num)
  simp only [zero_mul,add_zero] at hsource
  have hsourceS : Summable S := hsource.1
  have hrare := old_hessian_weak_rare_budget M hg 0 (by norm_num)
  have hC : Summable C := (hsourceS.mul_left (1/2:ℝ)).add hrare.1
  have hf (j : ℕ) : Integrable (f j) μ :=
    (old_hessian_cell_directional_term_moment M h hM hg N hpast m hm U hU e j).1
  have hn (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0≤f j ω := by
    unfold f oldHessianCellDirectionalTerm
    have hpref : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
      (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
    exact mul_nonneg (mul_nonneg (mul_nonneg hpref (pow_nonneg inverse_history_discount_range.1.le (2*j)))
      (add_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le) ENNReal.toReal_nonneg))
      (old_hessian_cell_directional_bounds M m U hU j e ω).1
  have hb (j : ℕ) : (∫ ω,f j ω ∂μ)≤C j*vecNormSq e := by
    have hh := (old_hessian_cell_directional_term_moment M h hM hg N hpast m hm U hU e j).2
    exact hh.trans_eq (by dsimp only [C,S]; ring)
  have hs := old_hessian_positive_series_integral μ f (fun j => C j*vecNormSq e)
    hf hn (hC.mul_right _) hb
  refine ⟨hs.1,hs.2.1,hs.2.2.trans ?_⟩
  rw [tsum_mul_right]
  have hbase : (∑' j,C j)≤(mixedXiPreCap M+(1/10^12:ℝ)*theta M)/2 := by
    change (∑' j, ((1/2:ℝ)*S j+oldHessianWeakRareBudget M 0 j))≤_
    rw [Summable.tsum_add (hsourceS.mul_left (1/2:ℝ)) hrare.1,tsum_mul_left]
    have hh := add_le_add (mul_le_mul_of_nonneg_left hsource.2 (by norm_num : (0:ℝ)≤1/2))
      (old_hessian_weak_rare_zero_half_reserve M hg)
    exact hh.trans_eq (by ring)
  exact mul_le_mul_of_nonneg_right (hbase.trans (div_le_div_of_nonneg_right
    (old_hessian_weak_payment_certified M hg) (by norm_num : (0:ℝ)≤2))) (vecNormSq_nonneg e)

end
end ASDExplicitGamma.Scalar
