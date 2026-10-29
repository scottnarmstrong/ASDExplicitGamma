module

public import ASDExplicitGamma.Native.OldSignedAffineContribution
public import ASDExplicitGamma.Native.OldSignedPartitionSeries
public import ASDExplicitGamma.Native.OldSignedFlatCellRegularity

/-! Assemble the two signed affine families into the literal AN (5.2)
contribution, with convergence established before adding complete sums. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- One flat family's signed mean deviation is a genuine complete series
on each physical cell. -/
theorem old_signed_flat_affine_family_cell_summable (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n => ∑ i : Fin 2,
      (let p := oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
       blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p)) := by
  apply summable_sum
  intro i _
  apply old_signed_affine_deviation_summable
  cases plus
  · exact old_signed_flat_minus_mean_series Q depth b L i U hU
  · exact old_signed_flat_plus_mean_series Q depth b L i U hU

/-- The complete spatially averaged affine family is summable without a
sign assumption on the deviation from the identity. -/
theorem old_signed_flat_affine_family_summable (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    Summable (fun n => descendantsAverage Q depth (fun U => ∑ i : Fin 2,
      (let p := oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
       blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p))) :=
  (old_signed_partition_series Q depth _
    (old_signed_flat_affine_family_cell_summable Q depth a b L plus)).1

/-- Adding the two complete signed affine families gives precisely Aff
in AN (5.2), retaining its pathwise sign. -/
theorem old_signed_flat_affine_family_sum (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let aff := fun plus n => descendantsAverage Q depth (fun U => ∑ i : Fin 2,
      (let p := oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)
       blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p))
    (∑' n,aff true n)+(∑' n,aff false n)=oldSignedFlatAffineContribution Q depth a b L := by
  intro aff
  rw [← (old_signed_flat_affine_family_summable Q depth a b L true).tsum_add
    (old_signed_flat_affine_family_summable Q depth a b L false)]
  unfold oldSignedFlatAffineContribution
  apply tsum_congr
  intro n
  change descendantsAverage Q depth _+descendantsAverage Q depth _=_
  rw [← descendantsAverage_add]
  unfold oldSignedFlatAffineMode
  congr 1
  funext U
  simp only [oldSignedFlatAffineCellMode,Finset.sum_add_distrib,oldSignedFlatInput,
    Bool.false_eq_true,ite_false,ite_true]

end
end ASDExplicitGamma.Native
