module

public import ASDExplicitGamma.Native.OldSignedPureSecondInverseReciprocal
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxySeries
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedActualCellPotentials
public import ASDExplicitGamma.Native.OldSignedSeriesLinearBudget

/-! Actual plus reciprocal defects with the directional affine budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- The actual plus reciprocal defect has the literal sharp affine
and pure-second oscillation bound in the same old-medium history. -/
theorem old_signed_actual_plus_reciprocal_directional_inverse_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := oldSignedFlatPlusBlock Q b L n i
    let Z := oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L true n i U hU
    let m := oldSignedBlockMean U F
    let O := oldSignedBlockPositiveNorm U (F-fun _ => m)
    vectorWeakHaarNorm U (fun x => (scalarCoefficientFlux
      (responseFramePlanarCoefficientField nu sigma kU) Z x).2-(F x).2) ≤
      Real.sqrt (oldSignedDirectionalProxy U (responseFramePlanarCoefficientField nu sigma kU) m.2)+
        (oldSignedInverseHistory U a+1)*O := by
  intro a hsub kU F Z m O
  have hm : oldSignedBlockMean U F=(0,m.2) := by
    simp [m,F,oldSignedFlatPlusBlock,oldSignedBlockMean,cubeAverage_const]
    rfl
  have hh := old_signed_pure_second_reciprocal_directional_inverse U nu sigma hnu hsigma
    (oldSignedCellCoefficient Q U hsub k) F
    (old_signed_flat_input_cell_memL2 Q depth b L true n i U hU)
    (fun _ => rfl) m.2 hm
    (old_signed_flat_input_cell_first_positive Q depth b L true n i U hU m.1)
    (old_signed_flat_input_cell_second_positive Q depth b L true n i U hU m.2)
  dsimp only at hh
  have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
  rw [hs.1] at hh
  exact hh

/-- The complete two-load reciprocal norm has constant-one
mean/oscillation aggregation; convergence is part of the conclusion. -/
theorem old_signed_actual_plus_reciprocal_directional_inverse_series (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let kU := oldSignedCellCoefficient Q U hsub k
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)
    let Z := fun n i => oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L true n i U hU
    let g := fun n i => vectorWeakHaarNorm U (fun x => (scalarCoefficientFlux
      (responseFramePlanarCoefficientField nu sigma kU) (Z n i) x).2-
        (oldSignedFlatPlusBlock Q b L n i x).2)
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,g n i^2) ∧
    Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,g n i^2) ≤
      Real.sqrt (∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField nu sigma kU) (m n i).2)+
        (oldSignedInverseHistory U a+1)*oldSignedFlatOscillationSize Q U b L true := by
  intro a hsub kU m Z g
  let p := fun n i => oldSignedDirectionalProxy U
    (responseFramePlanarCoefficientField nu sigma kU) (m n i).2
  let v := fun n i => Real.sqrt (p n i)
  let O := fun n i => oldSignedBlockPositiveNorm U
    (oldSignedFlatPlusBlock Q b L n i-fun _ => m n i)
  have hp0 (n : whiteBasisIndex) (i : Fin 2) : 0≤p n i :=
    (old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma kU (m n i).2).1
  have hps : Summable (fun n => ∑ i : Fin 2,p n i) :=
    old_signed_actual_plus_directional_proxy_series Q depth nu sigma hnu hsigma k b L U hU
  have hvs : Summable (fun n => ∑ i : Fin 2,v n i^2) := by
    simpa only [v,Real.sq_sqrt (hp0 _ _)] using hps
  have hOs : Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,O n i^2) :=
    old_signed_flat_oscillation_budget_series Q depth b L true U hU
  have hM : 0≤oldSignedInverseHistory U a :=
    lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hh := old_signed_load_series_linear_budget v O g
    (1:ℝ) ((oldSignedInverseHistory U a+1))
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (by norm_num) (add_nonneg hM (by norm_num)) hvs hOs
    (fun n i => by simpa only [one_mul] using
      old_signed_actual_plus_reciprocal_directional_inverse_bound Q depth nu sigma hnu hsigma k b L n i U hU)
  simpa only [v,Real.sq_sqrt (hp0 _ _),oldSignedFlatMeanSize,oldSignedFlatOscillationSize,
    oldSignedFlatInput,ite_true,O,m,p,one_mul] using hh

end
end ASDExplicitGamma.Native
