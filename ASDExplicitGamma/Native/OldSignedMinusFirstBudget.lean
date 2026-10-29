module

public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedActualCellPotentials
public import ASDExplicitGamma.Native.OldSignedSeriesLinearBudget

/-! Actual minus-flat first potentials and their complete joint square
budget, with all source regularity discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- The literal minus input is compatible on every child cell, by
restriction of its genuine parent zero-boundary potential. -/
theorem old_signed_actual_minus_cell_compatible (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    ScalarCompatible (openCubeSet U) (oldSignedFlatMinusBlock Q b L n i) := by
  obtain ⟨u,hu⟩ := old_signed_flat_minus_potential_zero_trace Q b L n i
  refine ⟨old_signed_flat_input_cell_memL2 Q depth b L false n i U hU,?_,?_⟩
  · refine ⟨u.toH1Function.restrict (isOpen_openCubeSet U)
      (openCubeSet_subset_of_mem_descendantsAtDepth hU),?_⟩
    exact hu
  · exact isSolenoidalOn_zero

/-- The constructed minus first potential has the literal sharp affine
and compatible oscillation bound in the same old-medium history. -/
theorem old_signed_actual_minus_first_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let F := oldSignedFlatMinusBlock Q b L n i
    let m := oldSignedBlockMean U F
    let O := oldSignedBlockPositiveNorm U (F-fun _ => m)
    vectorWeakHaarNorm U
      (oldSignedCellMinusPotential Q U hsub nu sigma hnu hsigma k b L n i).toH1Function.grad ≤
      Real.sqrt (oldSignedCorrectorHistory U a)*Real.sqrt (blockVecDot m m)+
        (Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)+1)*O := by
  intro a hsub F m O
  have hh := old_signed_flat_compatible_first_corrector U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U hsub k) F
    (old_signed_flat_input_cell_memL2 Q depth b L false n i U hU)
    (old_signed_flat_input_cell_first_positive Q depth b L false n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L false n i U hU m.2)
    (old_signed_actual_minus_cell_compatible Q depth b L n i U hU)
  dsimp only at hh
  have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
  rw [hs.1,hs.2.1,hs.2.2] at hh
  rw [old_signed_cell_minus_potential_grad]
  exact hh

/-- The complete two-load first-potential norm has constant-one
mean/oscillation aggregation; convergence is part of the conclusion. -/
theorem old_signed_actual_minus_first_series (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let g := fun n i => vectorWeakHaarNorm U
      (oldSignedCellMinusPotential Q U hsub nu sigma hnu hsigma k b L n i).toH1Function.grad
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,g n i^2) ∧
    Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,g n i^2) ≤
      Real.sqrt (oldSignedCorrectorHistory U a)*oldSignedFlatMeanSize Q U b L false+
        (Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)+1)*oldSignedFlatOscillationSize Q U b L false := by
  intro a hsub g
  let m := fun n i => oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)
  let v := fun n i => Real.sqrt (blockVecDot (m n i) (m n i))
  let O := fun n i => oldSignedBlockPositiveNorm U
    (oldSignedFlatMinusBlock Q b L n i-fun _ => m n i)
  have hm0 (n : whiteBasisIndex) (i : Fin 2) : 0≤blockVecDot (m n i) (m n i) :=
    add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have hvs : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,v n i^2) := by
    simp only [v,Real.sq_sqrt (hm0 _ _)]
    simpa [m,oldSignedFlatInput] using
      old_signed_flat_mean_budget_series Q depth b L false U hU
  have hOs : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,O n i^2) :=
    old_signed_flat_oscillation_budget_series Q depth b L false U hU
  have hh := old_signed_load_series_linear_budget v O g
    (Real.sqrt (oldSignedCorrectorHistory U a)) ((Real.sqrt (oldSignedInverseHistory U a*oldSignedResponseHistory U a)+1))
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (by norm_num)) hvs hOs
    (fun n i => old_signed_actual_minus_first_bound Q depth nu sigma hnu hsigma k b L n i U hU)
  simpa only [v,Real.sq_sqrt (hm0 _ _),oldSignedFlatMeanSize,oldSignedFlatOscillationSize,
    oldSignedFlatInput,Bool.false_eq_true,ite_false,O,m] using hh

end
end ASDExplicitGamma.Native
