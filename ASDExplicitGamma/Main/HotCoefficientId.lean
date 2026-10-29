module

public import ASDExplicitGamma.Main.EOscillationInverseHistoryAdapter
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Main.MixedBridgeDepthFive

/-! Identification of the coefficient families used by the hot trial (root-level
affine restriction of the inserted scalar), the OLD insertion skew coefficient, and the
cell-rooted coefficient of the local first corrector. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

local instance hotCoeffIdCubeCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The inserted scalar on the closure of any cube is the pointwise OLD skew entry. -/
theorem hot_inserted_scalar_entry (M : ABKModel 2) (P : TriadicCube 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (y : Vec 2) (hy : y ∈ closure (cubeSet P)) :
    modelInsertedScalar (closure (cubeSet P)) m t ω ⟨y, hy⟩ =
      Cutoff.cutoff m ω y 1 0 + Real.sqrt t * ω.1 (m + 1) y 1 0 := by
  classical
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact (closure (cubeSet P))
    (isBounded_cubeSet P).isCompact_closure
  have hmodel := modelInsertedScalar_apply (closure (cubeSet P)) M ell m hK t ω ⟨y, hy⟩
  have hmodelMatrix :
      (Model.partialInsertedCoefficient M m t ω).toFun y =
        M.nu • (1 : Mat 2) + Cutoff.cutoff m ω y +
          Real.sqrt t • Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell
            (ω.1 (m + 1)) y := by
    rw [mainInsertion_coefficient]
    ext i j
    simp [RegCoeffField.add_apply, RegCoeffField.smul_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
  have hentry :
      (Model.partialInsertedCoefficient M m t ω).toFun y 1 0 =
        Cutoff.cutoff m ω y 1 0 + Real.sqrt t * ω.1 (m + 1) y 1 0 := by
    have hh := congrArg (fun A : Mat 2 => A 1 0) hmodelMatrix
    simpa using hh
  rw [hmodel]
  exact hentry

/-- The root affine restriction of the inserted scalar is the OLD insertion skew coefficient. -/
theorem hot_root_coefficient_eq_skew (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mainAffineOpenResponseRestriction Q
        (modelInsertedScalar (closure (cubeSet Q)) m t ω) =
      mainInsertionSkewCoefficient m t Q ω := by
  classical
  apply BoundedContinuousFunction.ext
  intro x
  have hx : x.1 ∈ closure (cubeSet Q) := closure_mono (openCubeSet_subset_cubeSet Q) x.2
  have := hot_inserted_scalar_entry M Q m t ω x.1 hx
  simp only [mainAffineOpenResponseRestriction, mainAffineOpenClosureInclusion,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    BoundedContinuousFunction.compContinuous_apply, mainInsertionSkewCoefficient]
  exact this

/-- Restricting the root coefficient to a descendant cell gives the cell-rooted coefficient. -/
theorem hot_cell_coefficient_eq (M : ABKModel 2) (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    oldSignedCellCoefficient Q U hU
        (mainAffineOpenResponseRestriction Q
          (modelInsertedScalar (closure (cubeSet Q)) m t ω)) =
      mainAffineOpenResponseRestriction U
        (modelInsertedScalar (closure (cubeSet U)) m t ω) := by
  rw [hot_root_coefficient_eq_skew M Q m t ω, hot_root_coefficient_eq_skew M U m t ω]
  exact mainInsertionSkewCoefficient_cell_eq Q U hU m t ω

end

end ASDExplicitGamma.Main
