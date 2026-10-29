module

public import ASDExplicitGamma.Native.ParentBoundaryFlatVariance

/-! Exact geometry of the actual flat source cell means and variance loss. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic
noncomputable section

/-- The complete two-load doubled source norm is the actual four-coordinate
Hilbert energy, with the plus source sign preserved inside its square. -/
theorem parent_boundary_flat_cell_energy (Q : TriadicCube 2) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q depth) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i : whiteBasisIndex) :
    (∑ col : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus i col))=
      hilbertEnergy U (parentBoundaryFlatH1 Q b L plus i).toFun := by
  have hm := hilbert_memLp_descendant hU (parentBoundaryFlatH1 Q b L plus i).memL2_normalized
  rw [main_hilbertEnergy_euclidean U hm,Fintype.sum_prod_type]
  cases plus <;> simp [parentBoundaryFlatH1,mainFlatPlusH1,mainFlatMinusH1,mainHilbertH1OfCoordinates,
    oldSignedFlatInput,oldSignedFlatPlusBlock,oldSignedFlatMinusBlock,oldSignedBlockL2Energy,energy_const,energy_neg]

private theorem average_neg' (U : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage U (fun x => -f x) = -cubeAverage U f := by
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure,integral_neg]

/-- The actual two-load source cell means have exactly the Hilbert mean
norm, including the source's negative plus block. -/
theorem parent_boundary_flat_cell_mean (Q : TriadicCube 2) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q depth) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i : whiteBasisIndex) :
    (∑ col : Fin 2,blockVecDot
      (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col))
      (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col)))=
      ‖hilbertCubeAverage U (parentBoundaryFlatH1 Q b L plus i).toFun‖^2 := by
  let F := (parentBoundaryFlatH1 Q b L plus i).toFun
  have hm : MemLp F 2 (normalizedCubeMeasure U) :=
    hilbert_memLp_descendant hU (parentBoundaryFlatH1 Q b L plus i).memL2_normalized
  have he (a : Fin 2 × Fin 2) : (hilbertCubeAverage U F).ofLp a=cubeAverage U (fun x => (F x).ofLp a) := by
    let pr : EuclideanSpace ℝ (Fin 2 × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) a
    have hh := hilbertCubeAverage_map U pr hm
    change hilbertCubeAverage U (fun x => (F x).ofLp a)=(hilbertCubeAverage U F).ofLp a at hh
    rw [hilbertCubeAverage_real] at hh
    exact hh.symm
  change _=‖hilbertCubeAverage U F‖^2
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  cases plus <;> simp [F,parentBoundaryFlatH1,mainFlatPlusH1,mainFlatMinusH1,mainHilbertH1OfCoordinates,
    oldSignedFlatInput,oldSignedFlatPlusBlock,oldSignedFlatMinusBlock,oldSignedBlockMean,
    blockVecDot,vecDot,average_neg',cubeAverage_const,pow_two]

/-- The literal finite-cell source mean loss is exactly the same Hilbert
variance used by the sharp cell Poincare bound. -/
theorem parent_boundary_flat_cell_mean_loss (Q : TriadicCube 2) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q depth) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) (i : whiteBasisIndex) :
    (∑ col : Fin 2,oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus i col))-
      (∑ col : Fin 2,blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col))
        (oldSignedBlockMean U (oldSignedFlatInput Q b L plus i col)))=
      hilbertEnergy U (fun x => (parentBoundaryFlatH1 Q b L plus i).toFun x-
        hilbertCubeAverage U (parentBoundaryFlatH1 Q b L plus i).toFun) := by
  rw [parent_boundary_flat_cell_energy Q depth U hU,parent_boundary_flat_cell_mean Q depth U hU]
  exact (parent_boundary_hilbert_cell_variance_identity U _
    (hilbert_memLp_descendant hU (parentBoundaryFlatH1 Q b L plus i).memL2_normalized)).symm

end
end ASDExplicitGamma.Native
