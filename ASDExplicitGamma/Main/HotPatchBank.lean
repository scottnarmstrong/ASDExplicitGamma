module

public import ASDExplicitGamma.Main.HotObsSplit
public import ASDExplicitGamma.Main.HotPatchSourceBoundCells
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw

/-! Pathwise domination of the observer-cell inverse histories by the global bank carrier
`B* = mixedBridgeBstar`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response
open Algsuperdiff.Section3

noncomputable section

/-- Every depth-`hobs+5` cell of the observer root `originCube 2 (m+hobs)` (`hobs ≤ 40`) is a
bank source root. -/
theorem hot_cell_mem_observer_roots (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    U ∈ mixedBridgeObserverSourceRoots m := by
  have hparent : originCube 2 (m + hobs) ∈
      descendantsAtDepth (originCube 2 (m + 40)) (40 - hobs) := by
    have h := originCube_mem_descendantsAtDepth' 2 (m + 40) (40 - hobs)
    have e : m + 40 - ((40 - hobs : ℕ) : ℤ) = m + hobs := by
      push_cast [Nat.cast_sub h40]
      ring
    rwa [e] at h
  have hdepth := mem_descendantsAtDepth_add hparent hU
  have e2 : 40 - hobs + (hobs + 5) = 40 + 5 := by omega
  rw [e2] at hdepth
  unfold mixedBridgeObserverSourceRoots
  exact Finset.mem_biUnion.mpr ⟨5, Finset.mem_range.mpr (by norm_num), hdepth⟩

/-- Pathwise, the inverse history of every observer cell (in the observer-root frame field) is
at most the global bank carrier `B*`. -/
theorem hot_cell_history_le_bstar (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    oldSignedInverseHistory U
        (oldSignedPartialFrameFieldAt M (originCube 2 (m + hobs)) m t ω) ≤
      mixedBridgeBstar M m t ω := by
  classical
  let Q := originCube 2 (m + hobs)
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar_characterization M m).1
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closure (cubeSet Q))
    (isBounded_cubeSet Q).isCompact_closure
  have hsubU : openCubeSet U ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hEllRaw := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
    (measurableSet_openCubeSet U)
    (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet Q (hsubU hx))))
  have hEllFrame := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (mainAffineOpenResponseRestriction Q
      (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω))).mono
    (measurableSet_openCubeSet U) hsubU
  have hframe := pureFlux_inverseHistory_frame_eq U
    (Model.partialInsertedCoefficient M m t ω).toFun
    (oldSignedPartialFrameFieldAt M Q m t ω) hEllRaw hEllFrame hσ
    (q := (3 : ℝ) ^ (1 / 4 : ℝ))
    (fun R d hR => old_signed_partial_cell_frame_at M Q m t ω R (hobs + 5 + d)
      (mem_descendantsAtDepth_add hU hR))
  have hroots := hot_cell_mem_observer_roots m hobs h40 U hU
  have hprof : mixedBridgeRootHistoryProfile M m t ω U ≤ mixedBridgeBstar M m t ω := by
    unfold mixedBridgeBstar Book.Ch02.finsetSupReal
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨U, hroots, rfl⟩
  unfold mixedBridgeRootHistoryProfile at hprof
  unfold oldSignedInverseHistory
  rw [hframe]
  exact hprof

end

end ASDExplicitGamma.Main
