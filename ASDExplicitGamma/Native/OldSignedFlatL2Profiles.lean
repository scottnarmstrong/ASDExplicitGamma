module

public import ASDExplicitGamma.Native.OldSignedFlatCellRegularity
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! The full local L2 sizes x_U,y_U of AN (1.3), distinct from the
sharper cell-mean sizes used in the internal projection estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Normalized physical L2 energy of the two doubled blocks. -/
def oldSignedBlockL2Energy (U : TriadicCube 2) (F : Vec 2 → BlockVec 2) : ℝ :=
  (∑ j : Fin 2,energy U (fun x => (F x).1 j))+
    ∑ j : Fin 2,energy U (fun x => (F x).2 j)

/-- The actual full local L2 flat size x_U (plus) or y_U (minus) of AN. -/
def oldSignedFlatL2Size (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,
    oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus n i))

/-- Jensen's inequality retains the actual L2 input in the mean split. -/
theorem old_signed_block_mean_le_l2 (U : TriadicCube 2) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet U) F) :
    blockVecDot (oldSignedBlockMean U F) (oldSignedBlockMean U F)≤oldSignedBlockL2Energy U F := by
  have hf (j : Fin 2) : cubeAverage U (fun x => (F x).1 j)^2≤energy U (fun x => (F x).1 j) := by
    rw [←energy_projection_zero U (fun x => (F x).1 j)]
    exact energy_projection_le U 0 (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) j))
  have hg (j : Fin 2) : cubeAverage U (fun x => (F x).2 j)^2≤energy U (fun x => (F x).2 j) := by
    rw [←energy_projection_zero U (fun x => (F x).2 j)]
    exact energy_projection_le U 0 (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) j))
  have hh := add_le_add (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hf j))
    (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hg j))
  simpa only [oldSignedBlockMean,oldSignedBlockL2Energy,blockVecDot,vecDot,pow_two] using hh

/-- Both actual full flat L2 profiles have convergent complete mode series
on each chosen descendant cell. -/
theorem old_signed_flat_l2_budget_series (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,
      oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus n i)) := by
  cases plus
  · have hs (i j : Fin 2) := old_signed_l2_energy_descendant_series Q depth
      (fun n => (mainFlatMinusCoordinate Q b L n (i,j)).toFun)
      (fun n => (mainFlatMinusCoordinate Q b L n (i,j)).memL2_normalizedCubeMeasure)
      (old_signed_flat_minus_value_series Q b L (i,j)) U hU
    have hh := summable_sum (fun i (_ : i ∈ Finset.univ) => summable_sum (fun j (_ : j ∈ Finset.univ) => hs i j))
    simpa [oldSignedFlatInput,oldSignedBlockL2Energy,oldSignedFlatMinusBlock,energy_const] using hh
  · have hs (i j : Fin 2) := old_signed_l2_energy_descendant_series Q depth
      (fun n => (mainFlatPlusCoordinate Q b L n (i,j)).toFun)
      (fun n => (mainFlatPlusCoordinate Q b L n (i,j)).memL2_normalizedCubeMeasure)
      (old_signed_flat_plus_value_series Q b L (i,j)) U hU
    have hh := summable_sum (fun i (_ : i ∈ Finset.univ) => summable_sum (fun j (_ : j ∈ Finset.univ) => hs i j))
    simpa [oldSignedFlatInput,oldSignedBlockL2Energy,oldSignedFlatPlusBlock,energy_const,energy_neg] using hh

/-- The internal mean profile is bounded by the literal source L2 profile,
without any estimate premise or change of physical flat modes. -/
theorem old_signed_flat_mean_size_le_l2 (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    oldSignedFlatMeanSize Q U b L plus≤oldSignedFlatL2Size Q U b L plus := by
  apply Real.sqrt_le_sqrt
  exact (old_signed_flat_mean_budget_series Q depth b L plus U hU).tsum_le_tsum
    (fun n => Finset.sum_le_sum (fun i _ => old_signed_block_mean_le_l2 U _
      (old_signed_flat_input_cell_memL2 Q depth b L plus n i U hU)))
    (old_signed_flat_l2_budget_series Q depth b L plus U hU)

end
end ASDExplicitGamma.Native
