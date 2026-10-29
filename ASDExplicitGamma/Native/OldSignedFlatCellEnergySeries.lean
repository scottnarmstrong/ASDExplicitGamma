module

public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedAffineContribution
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport

/-! Complete actual flat-cell energy budgets with the signed affine
baseline and the constant-one joint mean/oscillation contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian
noncomputable section

/-- The actual cell projection energies are genuinely summable, and the
complete affine/oscillation bill retains the actual signed coarse baseline. -/
theorem old_signed_actual_flat_cell_energy_series (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let Z := fun n i => oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L plus n i U hU
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
    Summable (fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU (Z n i) (Z n i)) ∧
    (∑' n,∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU (Z n i) (Z n i)) ≤
      (∑' n,∑ i : Fin 2,blockVecDot (m n i)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (m n i)))+
      2*Real.sqrt (6*oldSignedCorrectorHistory U a)*
        (oldSignedFlatMeanSize Q U b L plus*oldSignedFlatOscillationSize Q U b L plus)+
      oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L plus^2 := by
  intro a kU Z m
  let O := fun n i => oldSignedBlockPositiveNorm U
    (oldSignedFlatInput Q b L plus n i-fun _ => m n i)
  let v := fun n i => Real.sqrt (blockVecDot (m n i) (m n i))
  let e := fun n => ∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU (Z n i) (Z n i)
  let c := fun n => ∑ i : Fin 2,blockVecDot (m n i)
    (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (m n i))
  have hm0 (n : whiteBasisIndex) (i : Fin 2) : 0≤blockVecDot (m n i) (m n i) :=
    add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  have hms (i : Fin 2) : Summable (fun n => blockVecDot (m n i) (m n i)) := by
    cases plus
    · exact old_signed_flat_minus_mean_series Q depth b L i U hU
    · exact old_signed_flat_plus_mean_series Q depth b L i U hU
  have hcs : Summable c := by
    apply summable_sum
    intro i _
    have hh := (old_signed_affine_deviation_summable
      (coarseBlockMatrix (openCubeSet U) a) (fun n => m n i) (hms i)).add (hms i)
    simpa only [sub_add_cancel] using hh
  have hvs : Summable (fun n => ∑ i : Fin 2,v n i^2) := by
    simpa only [v,Real.sq_sqrt (hm0 _ _)] using
      old_signed_flat_mean_budget_series Q depth b L plus U hU
  have hOs : Summable (fun n => ∑ i : Fin 2,O n i^2) :=
    old_signed_flat_oscillation_budget_series Q depth b L plus U hU
  have he (n : whiteBasisIndex) : 0≤e n := by
    apply Finset.sum_nonneg
    intro i _
    have hZ : MemBlockL2 (openCubeSet U) (Z n i) :=
      Lp.memLp (scalarResidualField U nu sigma hnu hsigma kU
        (toHilbertBlockL2OfBlockField (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU)))
    rw [←old_signed_energy_inner_fields U nu sigma hnu hsigma kU hZ hZ]
    exact real_inner_self_nonneg
  have hbound (n : whiteBasisIndex) : e n≤c n+
      (2*Real.sqrt (6*oldSignedCorrectorHistory U a))*(∑ i : Fin 2,v n i*O n i)+
      oldSignedResponseHistory U a*(∑ i : Fin 2,O n i^2) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      old_signed_actual_flat_cell_energy Q depth nu sigma hnu hsigma k b L plus n i U hU)
    simpa only [Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum] using hh
  have hh := old_signed_load_series_energy_budget e c v O
    (2*Real.sqrt (6*oldSignedCorrectorHistory U a)) (oldSignedResponseHistory U a)
    he (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hcs hvs hOs hbound
  have hO0 : 0≤∑' n,∑ i : Fin 2,O n i^2 :=
    tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hOeq : oldSignedFlatOscillationSize Q U b L plus^2=∑' n,∑ i : Fin 2,O n i^2 :=
    Real.sq_sqrt hO0
  rw [hOeq]
  simpa only [e,c,v,Real.sq_sqrt (hm0 _ _),oldSignedFlatMeanSize,oldSignedFlatOscillationSize,O,m] using hh

end
end ASDExplicitGamma.Native
