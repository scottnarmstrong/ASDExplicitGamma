module

public import ASDExplicitGamma.Native.OldSignedDirectionalInverseFlatCellSeries
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy
public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles

/-! The actual flat projection budget with its full L2 baseline and signed
identity-subtracted affine contribution, as used in AN (5.2). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- Split the actual coarse mean energy into its signed affine deviation
and an L2 baseline. No positivity of the affine deviation is required. -/
theorem old_signed_actual_plus_energy_baseline_directional (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k
    let Z := fun n i => oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L true n i U hU
    let m := fun n i => oldSignedBlockMean U (oldSignedFlatInput Q b L true n i)
    let aff := fun n => ∑ i : Fin 2,
      (blockVecDot (m n i) (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (m n i))-
        blockVecDot (m n i) (m n i))
    Summable aff ∧
    (∑' n,∑ i : Fin 2,oldSignedEnergyPairing U nu sigma kU (Z n i) (Z n i)) ≤
      (∑' n,∑ i : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L true n i))+
      (∑' n,aff n)+
      2*(Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*
        oldSignedFlatOscillationSize Q U b L true)+
      oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2 := by
  intro a kU Z m aff
  have hms (i : Fin 2) : Summable (fun n => blockVecDot (m n i) (m n i)) := by
    exact old_signed_flat_plus_mean_series Q depth b L i U hU
  have has : Summable aff := summable_sum (fun i _ =>
    old_signed_affine_deviation_summable (coarseBlockMatrix (openCubeSet U) a)
      (fun n => m n i) (hms i))
  have hmeans := old_signed_flat_mean_budget_series Q depth b L true U hU
  have hl2 := old_signed_flat_l2_budget_series Q depth b L true U hU
  have hmle : (∑' n,∑ i : Fin 2,blockVecDot (m n i) (m n i))≤
      ∑' n,∑ i : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L true n i) := by
    exact hmeans.tsum_le_tsum (fun n => Finset.sum_le_sum (fun i _ =>
      old_signed_block_mean_le_l2 U _
        (old_signed_flat_input_cell_memL2 Q depth b L true n i U hU))) hl2
  have hcoarse : (∑' n,∑ i : Fin 2,blockVecDot (m n i)
      (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) (m n i)))=
      (∑' n,aff n)+(∑' n,∑ i : Fin 2,blockVecDot (m n i) (m n i)) := by
    rw [← has.tsum_add hmeans]
    apply tsum_congr
    intro n
    simp only [aff,m,← Finset.sum_add_distrib,sub_add_cancel]
  have he := (old_signed_actual_plus_cell_energy_series_directional_inverse Q depth nu sigma hnu hsigma k b L U hU).2
  change _≤_ at he
  have hp : (∑' n,∑ i : Fin 2,oldSignedDirectionalProxy U
      (responseFramePlanarCoefficientField nu sigma kU) (m n i).2)=
      oldSignedFlatDirectionalMeanProxy Q U a b L true :=
    old_signed_flat_directional_proxy_cell_eq Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k b L true
  rw [hcoarse,hp] at he
  refine ⟨has,he.trans ?_⟩
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  simpa only [add_comm] using add_le_add (le_refl (∑' n,aff n)) hmle

end
end ASDExplicitGamma.Native
