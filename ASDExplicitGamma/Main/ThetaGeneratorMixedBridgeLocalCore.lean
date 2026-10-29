module

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

/-! Local depth-five OLD parent-gap carriers for MA-MIXED-BRIDGE. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Cold ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

noncomputable local instance mixedBridgeLocalBlockL2Measurable_Th'
    (U : TriadicCube 2) : MeasurableSpace (BlockL2 (openCubeSet U)) := borel _

local instance mixedBridgeLocalCubeCompact_Th'' (U : TriadicCube 2) :
    CompactSpace (closure (cubeSet U)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet U).isCompact_closure

noncomputable def mixedBridgeVLocal_Th (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  oldSignedPrimalErrorSize U U M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k

noncomputable def mixedBridgeGLocal_Th (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  oldSignedReciprocalErrorSize U U M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k

/-- The actual local first-corrector weak square on one descendant of the
depth-five source cell. The canonical fields and their coefficient are rooted
at `U`, with the original insertion label and OLD frame `m`. -/
noncomputable def mixedBridgeLocalCorrectorSq_Th (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ)
    (V : SquareCells U j) : ℝ := by
  let hV : openCubeSet V.val ⊆ openCubeSet U :=
    openCubeSet_subset_of_mem_descendantsAtDepth V.property
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  exact ∑ a : BlockCoord 2,
    vectorWeakHaarNorm V.val (fun x =>
      (oldSignedCellFirstCorrector U V.val hV M.nu σ M.nu_pos hσ k
        (oldSignedFrameCanonicalField U M.nu σ M.nu_pos hσ k (blockBasis a))
        (Lp.memLp (oldSignedFrameCanonicalField U M.nu σ M.nu_pos hσ k (blockBasis a)))).toH1Function.grad x) ^ 2

/-- Finite descendant average of the actual local first-corrector square. -/
noncomputable def mixedBridgeVLocalDepthSq_Th (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  Cold.squareCellMean U j (mixedBridgeLocalCorrectorSq_Th M m U t ω j)

/-- The weighted depth series of the local first-corrector weak energies. -/
noncomputable def mixedBridgeVl2Local_Th (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' j : ℕ,
    (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * mixedBridgeVLocalDepthSq_Th M m U t ω j

/-- The actual local first-corrector source size on `U`. -/
noncomputable def mixedBridgeVlLocal_Th (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (mixedBridgeVl2Local_Th M m U t ω)

end

end ASDExplicitGamma.Main
