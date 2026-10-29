module

public import ASDExplicitGamma.Main.HotPatchSourceBoundCells
public import ASDExplicitGamma.Native.OldSignedAffineCellResidual
public import ASDExplicitGamma.Native.OldSignedCellAverage
public import ASDExplicitGamma.Native.OldSignedErrorProfiles

/-! The tile-averaged weak size of the glued local correctors is the average of the squared
`U`-rooted primal error sizes `V_U²`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped BigOperators

noncomputable section

/-- On one source cell the four-load weak energy of the glued corrector is the squared
`U`-rooted primal error size `V_U²`. -/
theorem hot_corrector_cell_eq_primal_size (Q : TriadicCube 2) (D : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q D) :
    ∑ c : BlockCoord 2, vectorWeakHaarEnergy U (fun x i =>
        (hotGluedCorrector Q D nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad x i) =
      oldSignedPrimalErrorSize U U nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U
          (openCubeSet_subset_of_mem_descendantsAtDepth hU) k) ^ 2 := by
  classical
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  unfold oldSignedPrimalErrorSize
  rw [Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]
  apply Finset.sum_congr rfl
  intro c _
  rw [← ASDExplicitGamma.Inverse.hot_corrector_cell_weak_energy_eq Q D nu sigma hnu hsigma k (blockBasis c) U hU]
  have hcan := old_signed_affine_cell_residual Q U hsub nu sigma hnu hsigma k (blockBasis c)
  have hgrad : (fun x i => (oldSignedCellFirstCorrector Q U hsub nu sigma hnu hsigma k
      (fun _ => blockBasis c) (memLp_const (blockBasis c))).toH1Function.grad x i) =
      fun x i => ((oldSignedFrameCanonicalField U nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U hsub k) (blockBasis c)) x).1 i -
        (blockBasis c).1 i := by
    funext x i
    rw [old_signed_cell_first_corrector_grad]
    change ((oldSignedCellResidual Q U hsub nu sigma hnu hsigma k (fun _ => blockBasis c)
      (memLp_const (blockBasis c)) x).1 - (blockBasis c).1) i = _
    rw [hcan]
    rfl
  rw [hgrad]
  unfold vectorWeakHaarNorm
  rw [Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U _)]
  rfl

/-- Tile-averaged form. -/
theorem hot_corrector_tiled_eq_primal_sizes (Q : TriadicCube 2) (D : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    ∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q D
        (hotGluedCorrector Q D nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad =
      oldSignedCellAverage Q D (fun U => oldSignedPrimalErrorSize U.val U.val nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) ^ 2) := by
  classical
  unfold lemmaVTiledWeakEnergy
  rw [← Homogenization.descendantsAverage_sum Q D Finset.univ
    (fun U c => vectorWeakHaarEnergy U (fun x i =>
      (hotGluedCorrector Q D nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad x i))]
  rw [← old_signed_cell_average_eq_descendantsAverage]
  congr 1
  funext U
  exact hot_corrector_cell_eq_primal_size Q D nu sigma hnu hsigma k U.val U.property

end

end ASDExplicitGamma.Native
