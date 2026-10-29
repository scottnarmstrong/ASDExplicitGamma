module

public import ASDExplicitGamma.Main.HotPatchSourceBound
public import ASDExplicitGamma.Main.HotPatchCellWeak

/-! Package C with the cellwise `Vw² ≤ B* Δ` bound. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Native

/-- Package C with the cellwise package-A gap bound inserted: the coarse part of the hot
source is paid by `k_a (B* Δ)^{1/2}` for any bound `B*` on the cell inverse histories. -/
theorem hot_source_size_bound_of_cells (m : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 m) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (Bmax : ℝ)
    (hB : ∀ (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) depth),
      oldSignedInverseHistory U (responseFramePlanarCoefficientField nu sigma
        (oldSignedCellCoefficient (originCube 2 m) U
          (openCubeSet_subset_of_mem_descendantsAtDepth hU) k)) ≤ Bmax) :
    let Q := originCube 2 m
    let src : whiteBasisIndex → ℝ := fun n => ∑ c : BlockCoord 2,
      descendantsAverage Q depth (fun U => vectorPositiveHaarEnergy U (fun x =>
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2))
    Summable src ∧
    Real.sqrt (∑' n, src n) ≤
      oldSignedSourceMultiplier Q depth b L *
          Real.sqrt (Bmax * (descendantsAverage Q depth (fun U => traceDefect (openCubeSet U)
            (responseFramePlanarCoefficientField nu sigma k) 1) -
            traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1)) +
        mainKd (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q depth
          (hotGluedCorrector Q depth nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) := by
  intro Q src
  obtain ⟨hs, hbound⟩ := hot_source_size_bound m depth nu sigma hnu hsigma k b L hL
  refine ⟨hs, hbound.trans ?_⟩
  have hgap := hot_patch_drop_weak_bound_cells Q depth nu sigma hnu hsigma k Bmax hB
  have hx : (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q depth
      (hotPatchPotential Q depth nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) =
      descendantsAverage Q depth (fun U => ∑ c : BlockCoord 2, vectorWeakHaarEnergy U
        (fun x => (hotPatchDrop Q depth nu sigma hnu hsigma k (blockBasis c) x).1)) := by
    simp only [hotPatchPotential_grad, lemmaVTiledWeakEnergy]
    rw [main_descendantsAverage_finset_sum_univ]
  have hα : 0 ≤ oldSignedSourceMultiplier Q depth b L := by
    have hr := diagMeshRadius_pos Q depth
    unfold oldSignedSourceMultiplier
    positivity
  rw [hx]
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hgap) hα) le_rfl

end ASDExplicitGamma.Inverse
