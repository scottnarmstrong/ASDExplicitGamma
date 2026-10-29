module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellDirectionalJoin
public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation

/-! Deterministic varying cell/load weights consume the uniform directional cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Every individual directional proxy is nonnegative, including at samples
outside the event where its depth series is known to converge. -/
theorem old_hessian_cell_directional_theta_nonneg (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : 0≤oldHessianCellDirectionalTheta M m U e ω := by
  apply tsum_nonneg
  intro j
  unfold oldHessianCellDirectionalTerm
  have hp : 0≤1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  exact mul_nonneg (mul_nonneg (mul_nonneg hp (pow_nonneg inverse_history_discount_range.1.le (2*j)))
    (add_nonneg (mul_nonneg (by norm_num) (bankDepthFrame_pos M j).le) ENNReal.toReal_nonneg))
    (old_hessian_cell_directional_bounds M m U hU j e ω).1

/-- A deterministic vector may vary with the actual source cell. Its full
squared norm, rather than a constant-direction surrogate, pays Xi/2. -/
theorem old_hessian_cell_directional_weighted_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (q : OldSignedCellIndex (originCube 2 (m+129)) 134 → Vec 2) :
    Integrable (fun ω => oldSignedCellAverage (originCube 2 (m+129)) 134
      (fun U => oldHessianCellDirectionalTheta M m U.val (q U) ω)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldSignedCellAverage (originCube 2 (m+129)) 134
        (fun U => oldHessianCellDirectionalTheta M m U.val (q U) ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerXiExpr/2)*
        oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U => vecNormSq (q U)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q := originCube 2 (m+129)
  have hi U := (old_hessian_actual_cell_directional_theta M h hM hg N hpast m hm U.val U.property (q U)).2.1
  refine ⟨old_signed_cell_average_integrable μ Q 134 _ hi,?_⟩
  rw [old_signed_cell_average_integral μ Q 134 _ hi,←old_signed_cell_average_mul]
  exact old_signed_cell_average_mono Q 134 (fun U =>
    (old_hessian_actual_cell_directional_theta M h hM hg N hpast m hm U.val U.property (q U)).2.2)

/-- Countably many deterministic load columns can be summed after genuine
integrability; the full mean-square budget pays the complete family. -/
theorem old_hessian_cell_directional_weighted_series {ι : Type*} [Countable ι]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (q : ι → OldSignedCellIndex (originCube 2 (m+129)) 134 → Vec 2)
    (hq : Summable (fun j => oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U => vecNormSq (q j U)))) :
    let f := fun j ω => oldSignedCellAverage (originCube 2 (m+129)) 134
      (fun U => oldHessianCellDirectionalTheta M m U.val (q j U) ω)
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,Summable (fun j => f j ω)) ∧
      Integrable (fun ω => ∑' j,f j ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,∑' j,f j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerXiExpr/2)*
          ∑' j,oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U => vecNormSq (q j U)) := by
  intro f
  let C := Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.lowerXiExpr/2
  have hs := old_hessian_positive_series_integral (Cutoff.cutoffSampleLaw M).toMeasure f
    (fun j => C*oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U => vecNormSq (q j U)))
    (fun j => (old_hessian_cell_directional_weighted_mean M h hM hg N hpast m hm (q j)).1)
    (fun j ω => old_signed_cell_average_nonneg _ _ _ (fun U =>
      old_hessian_cell_directional_theta_nonneg M m U.val U.property (q j U) ω))
    (hq.mul_left C)
    (fun j => (old_hessian_cell_directional_weighted_mean M h hM hg N hpast m hm (q j)).2)
  rw [tsum_mul_left] at hs
  exact hs

end
end ASDExplicitGamma.Scalar
