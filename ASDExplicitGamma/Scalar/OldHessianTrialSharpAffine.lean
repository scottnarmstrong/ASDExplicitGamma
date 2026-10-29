module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineEnergy
public import ASDExplicitGamma.Scalar.OldHessianTrialMinusMeanBank

/-! Sharp deterministic bank for the original minus means: it is the exact
Dirichlet energy of the minus field, not merely the variance `b^2`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The complete original minus-mode means are square summable and their
actual spatial mean-square budget is at most the exact Dirichlet energy of the minus field. -/
theorem old_hessian_minus_mean_bank_sharp (Q : TriadicCube 2) (fine : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Summable (fun p : whiteBasisIndex×Fin 2 => oldSignedCellAverage Q fine
      (fun U => vecNormSq (oldHessianMinusMeanColumn Q fine b L p U))) ∧
      (∑' p : whiteBasisIndex×Fin 2,oldSignedCellAverage Q fine
        (fun U => vecNormSq (oldHessianMinusMeanColumn Q fine b L p U)))≤
        ∑' n,oldSignedFlatDirichletModeEnergy Q b L n := by
  let V := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) =>
    oldSignedBlockMean U.val (oldSignedFlatMinusBlock Q b L p.1 p.2)
  let F := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) => blockVecDot (V p U) (V p U)
  let G := fun (p : whiteBasisIndex×Fin 2) (U : OldSignedCellIndex Q fine) => vecNormSq (V p U).1
  have hF0 (p) (U) : 0≤F p U := add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have hG0 (p) (U) : 0≤G p U := vecNormSq_nonneg _
  have hGF (p) (U) : G p U≤F p U := le_add_of_nonneg_right (vecNormSq_nonneg _)
  have hFs (U : OldSignedCellIndex Q fine) : Summable (fun p => F p U) := by
    apply (summable_prod_of_nonneg (fun p => hF0 p U)).2
    refine ⟨fun _ => Summable.of_finite,?_⟩
    simpa only [tsum_fintype,oldSignedFlatInput,Bool.false_eq_true,ite_false,F,V] using
      old_signed_flat_mean_budget_series Q fine b L false U.val U.property
  have hGs (U : OldSignedCellIndex Q fine) : Summable (fun p => G p U) :=
    (hFs U).of_nonneg_of_le (fun p => hG0 p U) (fun p => hGF p U)
  have havg := old_signed_cell_average_series Q fine G hGs
  refine ⟨havg.1,?_⟩
  change (∑' p,oldSignedCellAverage Q fine (G p))≤∑' n,oldSignedFlatDirichletModeEnergy Q b L n
  rw [havg.2]
  have hmean (U : OldSignedCellIndex Q fine) : (∑' p,G p U)≤oldSignedFlatMeanSize Q U.val b L false^2 := by
    have hh := (hGs U).tsum_le_tsum (fun p => hGF p U) (hFs U)
    have he : (∑' p,F p U)=oldSignedFlatMeanSize Q U.val b L false^2 := by
      rw [(hFs U).tsum_prod]
      simp only [tsum_fintype]
      simpa only [oldSignedFlatInput,Bool.false_eq_true,ite_false,F,V] using
        (old_signed_flat_mean_size_sq Q U.val b L false).symm
    exact hh.trans_eq he
  have hh := old_signed_cell_average_mono Q fine hmean
  have hle := old_signed_cell_average_mono Q fine (fun U =>
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (old_signed_flat_mean_size_le_l2 Q fine b L false U.val U.property) 2)
  apply (hh.trans hle).trans
  rw [old_signed_cell_average_eq_descendantsAverage Q fine (fun U => oldSignedFlatL2Size Q U b L false^2)]
  rw [old_signed_flat_l2_size_partition,old_signed_flat_l2_size_sq]
  simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode]
  exact le_rfl


/-- Complete mode convergence, integrability and the original a5/2
annealed affine penalty, with no assumed energy or mean-square bound. -/
theorem old_hessian_minus_affine_energy_moment_sharp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,Summable (fun p => oldHessianMinusAffineEnergyTerm M m b L p ω)) ∧
    Integrable (oldHessianMinusAffineEnergy M m b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldHessianMinusAffineEnergy M m b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (1+evalReal scalarRealEnv lowerA5Expr/2)*∑' n,oldSignedFlatDirichletModeEnergy (originCube 2 (m+129)) b L n := by
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
  have hbank := old_hessian_minus_mean_bank_sharp Q 134 b L
  have hh := old_hessian_positive_series_integral μ (oldHessianMinusAffineEnergyTerm M m b L)
    (fun p => C*oldSignedCellAverage Q 134 (fun U => vecNormSq (q p U))) hi
    (old_hessian_minus_affine_energy_term_nonneg M m b L) (hbank.1.mul_left C) hb
  refine ⟨hh.1,hh.2.1,hh.2.2.trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hbank.2 (by norm_num [C,evalReal,lowerA5Expr,sc])

end
end ASDExplicitGamma.Scalar
