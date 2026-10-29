module

public import ASDExplicitGamma.Main.ThetaGeneratorMixedBridgeLocalCore
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpect
public import ASDExplicitGamma.Main.HotPatchSourceBound
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2

/-! MA-E-COVARIANCE, expectation step 6: the corrector energy `V_phi` of the hot patch is the
observer-tiling average of the local first-corrector squares `V_U^2`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

local instance hotCovCorrCompact_Th (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The restriction of the observer coefficient to a cell is the cell's own restricted
coefficient. -/
theorem hotCov_coef_restrict_eq_Th (M : ABKModel 2) (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    oldSignedCellCoefficient Q U hU (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)) =
    mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω) := by
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact (closure (cubeSet Q))
    (isBounded_cubeSet Q).isCompact_closure
  have hKU : closure (cubeSet U) ⊆ closure (cubeSet Q) :=
    closure_minimal ((cubeSet_subset_closure_openCubeSet U).trans
      (closure_mono (hU.trans (openCubeSet_subset_cubeSet Q)))) isClosed_closure
  have hKU' : closure (openCubeSet U) ⊆ closure (cubeSet Q) :=
    closure_mono (hU.trans (openCubeSet_subset_cubeSet Q))
  ext x
  simp only [oldSignedCellCoefficient, mainAffineOpenResponseRestriction,
    mainAffineOpenClosureInclusion, BoundedContinuousFunction.compContinuous_apply,
    BoundedContinuousFunction.compContinuousCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
  have hxQ : x.1 ∈ closure (cubeSet Q) := hKU' x.2
  have hxU : x.1 ∈ closure (cubeSet U) := closure_mono (openCubeSet_subset_cubeSet U) x.2
  have e1 : modelInsertedScalar (closure (cubeSet Q)) m t ω ⟨x.1, hxQ⟩ =
      Model.partialInsertedCoefficient M m t ω x.1 1 0 :=
    Gaussian.modelInsertedScalar_apply (closure (cubeSet Q)) M ell m hK t ω ⟨x.1, hxQ⟩
  have e2 : modelInsertedScalar (closure (cubeSet U)) m t ω ⟨x.1, hxU⟩ =
      Model.partialInsertedCoefficient M m t ω x.1 1 0 :=
    Gaussian.modelInsertedScalar_apply (closure (cubeSet U)) M ell m (hKU.trans hK) t ω
      ⟨x.1, hxU⟩
  exact e1.trans e2.symm

/-- The cell residual of the constant load is the canonical affine field of the cell. -/
theorem hotCov_cell_residual_const_Th (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedCellResidual Q U hU nu sigma hnu hsigma k (fun _ => P) (memLp_const P) =
      oldSignedFrameCanonicalField U nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k)
        P := by
  have hc (h : MemBlockL2 (openCubeSet U) (fun _ : Vec 2 => P)) :
      toHilbertBlockL2OfBlockField h =
        (scalarFrameRealization U nu sigma hnu hsigma
          (oldSignedCellCoefficient Q U hU k)).constantField P := by
    have hconst : toHilbertBlockL2OfBlockField h = blockVecToHilbertBlockL2Const P := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField h,
        coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet U) P] with x hx hy
      exact hx.trans hy.symm
    exact hconst.trans (by rfl)
  unfold oldSignedCellResidual
  show scalarResidualField U nu sigma hnu hsigma (oldSignedCellCoefficient Q U hU k)
    (toHilbertBlockL2OfBlockField _) = _
  rw [hc]
  exact old_signed_affine_residual_field U nu sigma hnu hsigma _ P

/-- On one cell, the corrector energy of the glued corrector is the local square `V_U^2`. -/
theorem hotCov_cell_vphi_eq_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    ∑ c : BlockCoord 2, vectorWeakHaarEnergy U
      (hotGluedCorrector (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1 (hotCovObsCoef_Th M m hobs t ω)
        (blockBasis c)).toH1Function.grad =
    mixedBridgeVLocal_Th M m U t ω ^ 2 := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  unfold mixedBridgeVLocal_Th oldSignedPrimalErrorSize
  rw [Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [vectorWeakHaarNorm, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
  rw [← ASDExplicitGamma.Inverse.hot_corrector_cell_weak_energy_eq _ _ _ _ M.nu_pos _ _ _ _ hU]
  have hgrad := old_signed_cell_first_corrector_grad (originCube 2 (m + hobs)) U hsub M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (hotCovObsCoef_Th M m hobs t ω) (fun _ => blockBasis c) (memLp_const _)
  have hres := hotCov_cell_residual_const_Th (originCube 2 (m + hobs)) U hsub M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (hotCovObsCoef_Th M m hobs t ω) (blockBasis c)
  have hcoef := hotCov_coef_restrict_eq_Th M (originCube 2 (m + hobs)) U hsub m t ω
  unfold hotCovObsCoef_Th at hgrad hres ⊢
  rw [hcoef] at hres
  have : (fun x i => (oldSignedCellFirstCorrector (originCube 2 (m + hobs)) U hsub M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
      (mainAffineOpenResponseRestriction (originCube 2 (m + hobs))
        (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 (m + hobs)))) m t ω))
      (fun _ => blockBasis c) (memLp_const _)).toH1Function.grad x i) =
      fun x => (oldSignedFrameCanonicalField U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainAffineOpenResponseRestriction U
          (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)) (blockBasis c) x).1 -
        (blockBasis c).1 := by
    funext x
    rw [hgrad]
    simp only [hres]
  rw [this]

/-- The total corrector energy of the hot patch is the observer average of `V_U^2`. -/
theorem hotCov_vphi_eq_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    ∑ c : BlockCoord 2, lemmaVTiledWeakEnergy (originCube 2 (m + hobs)) (hobs + 5)
      (hotGluedCorrector (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1 (hotCovObsCoef_Th M m hobs t ω)
        (blockBasis c)).toH1Function.grad = mainHotObsVl2_Th M m hobs t ω := by
  unfold lemmaVTiledWeakEnergy mainHotObsVl2_Th descendantsAverage
  simp only []
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun U hU => hotCov_cell_vphi_eq_Th M m hobs t ω U hU

end

end ASDExplicitGamma.Main
