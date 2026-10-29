module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellMatrixMoment
public import ASDExplicitGamma.Native.OldSignedCellAverageExpectation
public import ASDExplicitGamma.Native.OldSignedFlatProfileCaps

/-! Physical spatial matrix/corrector bills on the unchanged fine partition. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual fine matrix history paired with the original minus oscillations. -/
def oldHessianFlatMatrixEnergy (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U =>
    oldHessianCellMatrixMajorant M m U.val ω*
      oldSignedFlatOscillationSize (originCube 2 (m+129)) U.val b L false^2)

/-- Matrix oscillations retain the full physical deterministic spatial weight. -/
theorem old_hessian_flat_matrix_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldHessianFlatMatrixEnergy M m b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianFlatMatrixEnergy M m b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      evalReal scalarRealEnv lowerMExpr*descendantsAverage (originCube 2 (m+129)) 134
        (fun U => oldSignedFlatOscillationSize (originCube 2 (m+129)) U b L false^2) := by
  let Q := originCube 2 (m+129)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun (U : OldSignedCellIndex Q 134) => oldHessianCellMatrixMajorant M m U.val
  have hmom (U : OldSignedCellIndex Q 134) := old_hessian_cell_matrix_moments M h hM hg N hpast m hm U.val U.property
  have hnon (U : OldSignedCellIndex Q 134) ω : 0≤F U ω := add_nonneg
    (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (old_hessian_cell_max_trace_nonneg M m U.val U.property ω))) (Real.sqrt_nonneg _)
  have hcap (U : OldSignedCellIndex Q 134) := (old_signed_history_first_second_moments μ (F U)
    (evalReal scalarRealEnv lowerMExpr) (hmom U).1 (hnon U)
    (by norm_num [evalReal,lowerMExpr,sc]; positivity) (hmom U).2.1).1
  have hh := old_signed_cell_weighted_expectation μ Q 134 F
    (fun U => oldSignedFlatOscillationSize Q U.val b L false^2)
    (evalReal scalarRealEnv lowerMExpr) (fun U => (hmom U).1.integrable (by norm_num))
    (fun _ => sq_nonneg _) hcap
  refine ⟨hh.1,?_⟩
  rw [old_signed_cell_average_eq_descendantsAverage Q 134
    (fun U => oldSignedFlatOscillationSize Q U b L false^2)] at hh
  exact hh.2

/-- Correlated inverse-bank matrix oscillations pay beta Mstar, without
replacing the bank by an independent copy or by a pointwise constant. -/
theorem old_hessian_flat_banked_matrix_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (fun ω => oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b L ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b L ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      ((14103/10000:ℝ)*evalReal scalarRealEnv lowerMExpr)*descendantsAverage (originCube 2 (m+129)) 134
        (fun U => oldSignedFlatOscillationSize (originCube 2 (m+129)) U b L false^2) := by
  let Q := originCube 2 (m+129)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun (U : OldSignedCellIndex Q 134) ω =>
    oldHessianGroupedBank M m ω*oldHessianCellMatrixMajorant M m U.val ω
  have hc (U : OldSignedCellIndex Q 134) := old_hessian_cell_bank_matrix_moment M h hM hg N hpast m hm U.val U.property
  have hh := old_signed_cell_weighted_expectation μ Q 134 F
    (fun U => oldSignedFlatOscillationSize Q U.val b L false^2)
    ((14103/10000:ℝ)*evalReal scalarRealEnv lowerMExpr) (fun U => (hc U).1)
    (fun _ => sq_nonneg _) (fun U => (hc U).2)
  have he : (fun ω => oldHessianGroupedBank M m ω*oldHessianFlatMatrixEnergy M m b L ω)=
      (fun ω => oldSignedCellAverage Q 134 (fun U => F U ω*
        oldSignedFlatOscillationSize Q U.val b L false^2)) := by
    funext ω
    rw [oldHessianFlatMatrixEnergy,←old_signed_cell_average_mul]
    apply congrArg (oldSignedCellAverage Q 134)
    funext U
    exact (mul_assoc _ _ _).symm
  rw [he]
  refine ⟨hh.1,?_⟩
  rw [old_signed_cell_average_eq_descendantsAverage Q 134
    (fun U => oldSignedFlatOscillationSize Q U b L false^2)] at hh
  exact hh.2

end
end ASDExplicitGamma.Scalar
