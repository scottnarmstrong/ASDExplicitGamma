module

public import ASDExplicitGamma.Native.OldSignedCenteredPositive

/-! Actual complete flat mean and oscillation quantities for the internal
AN projection estimates, with genuine mode-series convergence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
noncomputable section

/-- Select the literal actual plus or minus input, preserving its block
and source sign before taking any local means. -/
def oldSignedFlatInput (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → BlockVec 2 :=
  if plus then oldSignedFlatPlusBlock Q b L n i else oldSignedFlatMinusBlock Q b L n i

/-- Complete cell-mean size, bounded by the full x_U or y_U of AN. -/
def oldSignedFlatMeanSize (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,
    blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))
      (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)))

/-- Complete actual positive oscillation size OmegaPlus/OmegaMinus,
with the actual cell mean removed from each physical flat mode. -/
def oldSignedFlatOscillationSize (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  Real.sqrt (∑' n : whiteBasisIndex,∑ i : Fin 2,
    oldSignedBlockPositiveNorm U (oldSignedFlatInput Q b L plus n i-
      fun _ => oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))^2)

/-- The plus-flat actual centered block-positive square series converges. -/
theorem old_signed_flat_plus_oscillation_series (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => oldSignedBlockPositiveNorm U
      (oldSignedFlatPlusBlock Q b L n i-fun _ => oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))^2) := by
  apply (old_signed_flat_plus_source_cell_energy_summable Q depth b L i U hU).of_nonneg_of_le (fun n => sq_nonneg _)
  intro n
  have hF := (old_signed_flat_plus_block_memL2 Q b L n i).mono_measure
    (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  rw [old_signed_block_positive_centering U _ hF]
  have he : oldSignedBlockPositiveNorm U (oldSignedFlatPlusBlock Q b L n i)^2=
      Triadic.vectorPositiveHaarNorm U (fun x => (oldSignedFlatPlusBlock Q b L n i x).2)^2 :=
    old_signed_pure_second_block_positive_sq U _
  rw [he]
  exact sub_le_self _ (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))

/-- The minus-flat actual centered block-positive square series converges. -/
theorem old_signed_flat_minus_oscillation_series (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => oldSignedBlockPositiveNorm U
      (oldSignedFlatMinusBlock Q b L n i-fun _ => oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))^2) := by
  apply (old_signed_flat_minus_source_cell_energy_summable Q depth b L i U hU).of_nonneg_of_le (fun n => sq_nonneg _)
  intro n
  have hF := (old_signed_flat_minus_block_memL2 Q b L n i).mono_measure
    (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU))
  rw [old_signed_block_positive_centering U _ hF]
  have he : oldSignedBlockPositiveNorm U (oldSignedFlatMinusBlock Q b L n i)^2=
      Triadic.vectorPositiveHaarNorm U (fun x => (oldSignedFlatMinusBlock Q b L n i x).1)^2 :=
    old_signed_pure_first_block_positive_sq U _
  rw [he]
  exact sub_le_self _ (add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))

/-- The actual complete mean budget converges for either physical flat input. -/
theorem old_signed_flat_mean_budget_series (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,
      blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))
        (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))) := by
  cases plus
  · exact summable_sum (fun i _ => old_signed_flat_minus_mean_series Q depth b L i U hU)
  · exact summable_sum (fun i _ => old_signed_flat_plus_mean_series Q depth b L i U hU)

/-- The complete actual oscillation budget converges for either input. -/
theorem old_signed_flat_oscillation_budget_series (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,oldSignedBlockPositiveNorm U
      (oldSignedFlatInput Q b L plus n i-fun _ => oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))^2) := by
  cases plus
  · exact summable_sum (fun i _ => old_signed_flat_minus_oscillation_series Q depth b L i U hU)
  · exact summable_sum (fun i _ => old_signed_flat_plus_oscillation_series Q depth b L i U hU)

end
end ASDExplicitGamma.Native
