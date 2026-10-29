module

public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedSeriesLinearBudget

/-! The complete actual reciprocal-error budgets (6.1) for both flat
sources, with all load and mode correlations retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Each actual flat reciprocal-error family has its sharp complete
mean/oscillation norm bound and genuine square summability. -/
theorem old_signed_actual_flat_reciprocal_series (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let F := fun n i => oldSignedFlatInput Q b L plus n i
    let Z := fun n i => oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U hU
    let g := fun n i => vectorWeakHaarNorm U (fun x =>
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (Z n i x)).2-(F n i x).2)
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,g n i^2) ∧
    Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,g n i^2) ≤
      Real.sqrt (6*oldSignedCorrectorHistory U a)*oldSignedFlatMeanSize Q U b L plus+
        (oldSignedResponseHistory U a+1)*oldSignedFlatOscillationSize Q U b L plus := by
  intro a kU F Z g
  let m := fun n i => oldSignedBlockMean U (F n i)
  let v := fun n i => Real.sqrt (blockVecDot (m n i) (m n i))
  let O := fun n i => oldSignedBlockPositiveNorm U (F n i-fun _ => m n i)
  have hm0 (n : whiteBasisIndex) (i : Fin 2) : 0≤blockVecDot (m n i) (m n i) :=
    add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have hvs : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,v n i^2) := by
    simpa only [v,Real.sq_sqrt (hm0 _ _)] using
      old_signed_flat_mean_budget_series Q depth b L plus U hU
  have hOs : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,O n i^2) :=
    old_signed_flat_oscillation_budget_series Q depth b L plus U hU
  have hM : 0≤oldSignedResponseHistory U a := ENNReal.toReal_nonneg
  have hh := old_signed_load_series_linear_budget v O g
    (Real.sqrt (6*oldSignedCorrectorHistory U a)) (oldSignedResponseHistory U a+1)
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (add_nonneg hM (by norm_num)) hvs hOs
    (fun n i => old_signed_actual_flat_cell_reciprocal Q depth nu sigma hnu hsigma k b L plus n i U hU)
  simpa only [v,Real.sq_sqrt (hm0 _ _),oldSignedFlatMeanSize,oldSignedFlatOscillationSize,O,m,F] using hh

end
end ASDExplicitGamma.Native
