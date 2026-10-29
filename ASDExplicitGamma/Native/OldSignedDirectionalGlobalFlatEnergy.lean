module

public import ASDExplicitGamma.Native.OldSignedDirectionalFlatBaseline
public import ASDExplicitGamma.Native.OldSignedFlatL2Partition
public import ASDExplicitGamma.Native.OldSignedFlatPatchedData
public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound

/-! The full actual flat energy bill after spatial assembly. Its affine
term remains signed and its full L2 baseline is the physical parent one. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- Actual complete flat projection energy, with the parent L2 baseline,
the signed spatial affine contribution, and the joint local oscillation bill. -/
theorem old_signed_global_plus_energy_bill_directional (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := fun n i => oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L true n i
    let f := fun n => ∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k (Z n i) (Z n i)
    let aff := fun n U => ∑ i : Fin 2,
      (let p := oldSignedBlockMean U (oldSignedFlatInput Q b L true n i)
       blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p)
    Summable f ∧
    (∑' n,f n)≤
      (∑' n,∑ i : Fin 2,oldSignedBlockL2Energy Q (oldSignedFlatInput Q b L true n i))+
      (∑' n,descendantsAverage Q depth (aff n))+
      descendantsAverage Q depth (fun U =>
        2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*
          oldSignedFlatOscillationSize Q U b L true+
        oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2) := by
  intro a Z f aff
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    let Z := fun i => oldSignedFlatCellResidual Q depth nu sigma hnu hsigma k b L true n i U.val U.property
    ∑ i : Fin 2,oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (Z i) (Z i)
  have he : f=(fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    change (∑ i : Fin 2,oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k _ _)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k _ _))=_
    simp_rw [old_signed_local_residual_cell_pairing]
    rw [old_signed_cell_average_sum]
    rfl
  let lc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    ∑ i : Fin 2,oldSignedBlockL2Energy U.val (oldSignedFlatInput Q b L true n i)
  let ac := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) => aff n U.val
  let B := fun U : OldSignedCellIndex Q depth =>
    2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U.val a b L true)*
      oldSignedFlatOscillationSize Q U.val b L true+
    oldSignedInverseHistory U.val a*oldSignedFlatOscillationSize Q U.val b L true^2
  have hsE (U : OldSignedCellIndex Q depth) : Summable (fun n => fc n U) :=
    (old_signed_actual_plus_cell_energy_series_directional_inverse Q depth nu sigma hnu hsigma k b L U.val U.property).1
  have hsL (U : OldSignedCellIndex Q depth) : Summable (fun n => lc n U) :=
    old_signed_flat_l2_budget_series Q depth b L true U.val U.property
  have hsA (U : OldSignedCellIndex Q depth) : Summable (fun n => ac n U) :=
    (old_signed_actual_plus_energy_baseline_directional Q depth nu sigma hnu hsigma k b L U.val U.property).1
  have hb (U : OldSignedCellIndex Q depth) : (∑' n,fc n U)≤
      (∑' n,lc n U)+(∑' n,ac n U)+B U := by
    have hh := (old_signed_actual_plus_energy_baseline_directional Q depth nu sigma hnu hsigma k b L U.val U.property).2
    exact hh.trans_eq (by dsimp only [B]; ring)
  have hh := old_signed_cell_average_series_upper Q depth fc _ hsE hb
  have heL : oldSignedCellAverage Q depth (fun U => ∑' n,lc n U)=
      ∑' n,∑ i : Fin 2,oldSignedBlockL2Energy Q (oldSignedFlatInput Q b L true n i) := by
    rw [← (old_signed_cell_average_series Q depth lc hsL).2]
    apply tsum_congr
    intro n
    change oldSignedCellAverage Q depth (fun U => ∑ i : Fin 2,
      oldSignedBlockL2Energy U.val (oldSignedFlatInput Q b L true n i))=_
    rw [old_signed_cell_average_eq_descendantsAverage Q depth (fun U => ∑ i : Fin 2,
      oldSignedBlockL2Energy U (oldSignedFlatInput Q b L true n i))]
    exact (old_signed_flat_l2_mode_partition Q depth b L true n).symm
  have heA : oldSignedCellAverage Q depth (fun U => ∑' n,ac n U)=
      ∑' n,descendantsAverage Q depth (aff n) := by
    rw [← (old_signed_cell_average_series Q depth ac hsA).2]
    apply tsum_congr
    intro n
    exact old_signed_cell_average_eq_descendantsAverage Q depth (aff n)
  rw [he]
  refine ⟨hh.1,?_⟩
  have hb' := hh.2
  rw [old_signed_cell_average_add,old_signed_cell_average_add,heL,heA] at hb'
  apply hb'.trans_eq
  congr 1
  exact old_signed_cell_average_eq_descendantsAverage Q depth (fun U =>
    2*Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)*
      oldSignedFlatOscillationSize Q U b L true+
    oldSignedInverseHistory U a*oldSignedFlatOscillationSize Q U b L true^2)

end
end ASDExplicitGamma.Native
