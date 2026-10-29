module

public import ASDExplicitGamma.Scalar.OldHessianTrialFineTopMean
public import ASDExplicitGamma.Scalar.OldHessianTrialPositiveSeries

/-! Complete actual affine energy of the unchanged fine minus field. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- One original minus-mode affine energy, before the physical mode sum. -/
def oldHessianMinusAffineEnergyTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (p : whiteBasisIndex×Fin 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 (m+129)) 134 (fun U =>
    let e := oldHessianMinusMeanColumn (originCube 2 (m+129)) 134 b L p U
    vecDot e (matVecMul (coarseBlockMatrix (openCubeSet U.val)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω))).upperLeft e))

/-- The literal complete affine energy with both bottom-source load labels. -/
def oldHessianMinusAffineEnergy (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' p,oldHessianMinusAffineEnergyTerm M m b L p ω

/-- Every mode has nonnegative physical affine energy. -/
theorem old_hessian_minus_affine_energy_term_nonneg (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (p : whiteBasisIndex×Fin 2) (ω : Cutoff.CutoffSample 2) :
    0≤oldHessianMinusAffineEnergyTerm M m b L p ω := by
  apply old_signed_cell_average_nonneg
  intro U
  have hn := old_hessian_top_quadratic_nonneg U.val M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (oldSignedCellCoefficient (originCube 2 (m+129)) U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) (oldHessianOldOpenCoefficient (m+129) m ω))
    (oldHessianMinusMeanColumn (originCube 2 (m+129)) 134 b L p U)
  rw [old_signed_cell_coarse_matrix_eq] at hn
  exact hn

/-- Complete mode convergence, integrability and the original a5/2
annealed affine penalty, with no assumed energy or mean-square bound. -/
theorem old_hessian_minus_affine_energy_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,Summable (fun p => oldHessianMinusAffineEnergyTerm M m b L p ω)) ∧
    Integrable (oldHessianMinusAffineEnergy M m b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianMinusAffineEnergy M m b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (1+evalReal scalarRealEnv lowerA5Expr/2)*b^2 := by
  let Q := originCube 2 (m+129)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let C := 1+evalReal scalarRealEnv lowerA5Expr/2
  let q := oldHessianMinusMeanColumn Q 134 b L
  let f := fun p (U : OldSignedCellIndex Q 134) ω => vecDot (q p U)
    (matVecMul (coarseBlockMatrix (openCubeSet U.val)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω))).upperLeft (q p U))
  have hc p U := old_hessian_fine_top_quadratic_mean M h hM hg N hpast m hm U (q p U)
  have hi p := old_signed_cell_average_integrable μ Q 134 (f p) (fun U => (hc p U).1)
  have hb p : (∫ ω,oldHessianMinusAffineEnergyTerm M m b L p ω ∂μ)≤
      C*oldSignedCellAverage Q 134 (fun U => vecNormSq (q p U)) := by
    change (∫ ω,oldSignedCellAverage Q 134 (fun U => f p U ω) ∂μ)≤_
    rw [old_signed_cell_average_integral μ Q 134 (f p) (fun U => (hc p U).1),
      ←old_signed_cell_average_mul]
    exact old_signed_cell_average_mono Q 134 (fun U => (hc p U).2)
  have hbank := old_hessian_minus_mean_bank Q 134 b L
  have hh := old_hessian_positive_series_integral μ (oldHessianMinusAffineEnergyTerm M m b L)
    (fun p => C*oldSignedCellAverage Q 134 (fun U => vecNormSq (q p U))) hi
    (old_hessian_minus_affine_energy_term_nonneg M m b L) (hbank.1.mul_left C) hb
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hbank.2 (by norm_num [C,evalReal,lowerA5Expr,sc])

end
end ASDExplicitGamma.Scalar
