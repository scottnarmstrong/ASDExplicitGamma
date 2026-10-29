module

public import ASDExplicitGamma.Main.DirectionalCovarianceTrace
public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeRootTheta
public import ASDExplicitGamma.Inverse.BankDepthObservers
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Cold.SquarePartitionProjection
public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! Observer-cell bank coefficient bounds (generalized copies of private lemmas
in `DirectionalCovarianceTrace'`). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Native ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Cold
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Scalar
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem obs_squareCellMean_eq_descendantsAverage
    (Q : TriadicCube 2) (j : ℕ) (f : TriadicCube 2 → ℝ) :
    Cold.squareCellMean Q j (fun C => f C.1) = descendantsAverage Q j f := by
  unfold Cold.squareCellMean descendantsAverage
  congr 1
  exact Finset.sum_attach (descendantsAtDepth Q j) f

theorem obs_partial_trace_cell_eq_raw
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : CutoffSample 2) (Q : TriadicCube 2) (a : CoeffField 2)
    (hfield : ∀ x ∈ openCubeSet Q,
      a x = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x)
    (R : TriadicCube 2) (j : ℕ) (hR : R ∈ descendantsAtDepth Q j) :
    traceDefect (openCubeSet R) a 1 = rawCubeFourLoadTrace M m R t ω := by
  have hRsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_openCubeSet R)).mono
    (fun x hx => hfield x (hRsub hx))
  have htrace : traceDefect (openCubeSet R) a 1 =
      traceDefect (openCubeSet R)
        ((Annealed.sigmaBar M m : ℝ)⁻¹ •
          (Model.partialInsertedCoefficient M m t ω).toFun) 1 := by
    unfold traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hae]
    rfl
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hRcube : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
    (measurableSet_cubeSet R) (fun x hx => hK (subset_closure (hRcube hx)))
  have hframe := Cold.cold_trace_frame M.nu_pos hEll
    (Annealed.sigmaBar_characterization M m).1
  change traceDefect (openCubeSet R) a 1 =
    traceDefect (cubeSet R)
      (Model.partialInsertedCoefficient M m t ω).toFun
      (Annealed.sigmaBar M m : ℝ)
  exact htrace.trans hframe

theorem obs_source_trace_average_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : CutoffSample 2) (Q : TriadicCube 2) (a : CoeffField 2)
    (hfield : ∀ x ∈ openCubeSet Q,
      a x = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x) (j : ℕ) :
    descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
      rawWeakTraceSequence M m Q t ω j := by
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      traceDefect (openCubeSet R) a 1 = rawCubeFourLoadTrace M m R t ω :=
    obs_partial_trace_cell_eq_raw M m t ht ω Q a hfield R j hR
  calc
    descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
        descendantsAverage Q j (fun R => rawCubeFourLoadTrace M m R t ω) := by
      unfold descendantsAverage
      dsimp only
      apply congrArg (fun x : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * x)
      apply Finset.sum_congr rfl
      intro R hR
      exact hcell R hR
    _ = rawWeakTraceSequence M m Q t ω j := by
      unfold rawWeakTraceSequence
      exact (obs_squareCellMean_eq_descendantsAverage Q j
        (fun R => rawCubeFourLoadTrace M m R t ω)).symm

private theorem obs_bank_response_max_eq_finsetSup
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty)
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : CutoffSample 2) :
    bankFiniteRootResponseMax s M m J weights ω =
      ENNReal.ofReal (Book.Ch02.finsetSupReal s
        (fun R => rootInverseResponse M R m J weights ω)) := by
  classical
  have huniv : (Finset.univ : Finset ↥s) = s.attach := by
    ext R
    simp
  calc
    bankFiniteRootResponseMax s M m J weights ω =
        (Finset.univ : Finset ↥s).sup
          (fun R => ENNReal.ofReal (rootInverseResponse M R.1 m J weights ω)) := by
      simp only [bankFiniteRootResponseMax, historyFiniteMax]
    _ = s.attach.sup
        (fun R => ENNReal.ofReal (rootInverseResponse M R.1 m J weights ω)) := by
      rw [huniv]
    _ = s.sup (fun R => ENNReal.ofReal (rootInverseResponse M R m J weights ω)) := by
      exact Finset.sup_attach s
        (fun R => ENNReal.ofReal (rootInverseResponse M R m J weights ω))
    _ = ENNReal.ofReal (Book.Ch02.finsetSupReal s
        (fun R => rootInverseResponse M R m J weights ω)) :=
      (ennreal_finset_sup_ofReal s hs _).symm

theorem observer_depth_max_le_bank_coefficient
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : CutoffSample 2) (Q : TriadicCube 2)
    (s jj : ℕ) (hQroot : Q ∈ descendantsAtDepth (originCube 2 (m + 40)) s)
    (a : CoeffField 2) {lamA LamA : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (hfield : ∀ x ∈ openCubeSet Q,
      a x = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x)
    (j : ℕ) (hsj : s + jj = 45 + j) :
    lemmaVInverseDepthMax Q a jj ≤ mixedOldDepthCoefficient M m t j ω := by
  classical
  let σ : ℝ := Annealed.sigmaBar M m
  let c : CoeffField 2 := (Model.partialInsertedCoefficient M m t ω).toFun
  let D : Finset (TriadicCube 2) :=
    bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j
  let Y : ℝ := (bankFiniteRootResponseMax D M m (m + 40)
    (bankPartialInsertionWeights m 1 t) ω).toReal
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hEllCopen : IsEllipticFieldOn M.nu
      ((2 * 2 * (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (openCubeSet Q) c :=
    Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
      (measurableSet_openCubeSet Q)
      (fun x hx => hK (subset_closure (openCubeSet_subset_cubeSet Q hx)))
  have hEllCcube : IsEllipticFieldOn M.nu
      ((2 * 2 * (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (cubeSet Q) c :=
    Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
      (measurableSet_cubeSet Q) (fun x hx => hK (subset_closure hx))
  have hmatrix (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q jj) :
      coarseBlockMatrix (cubeSet R) a =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) c) := by
    have hfieldR : (fun x => a x) =ᵐ[volumeMeasureOn (openCubeSet R)]
        (σ⁻¹ • c) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet R)]
        with x hx
      exact hfield x
        (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have hcoarse : coarseBlockMatrix (cubeSet R) a =
        coarseBlockMatrix (cubeSet R) (σ⁻¹ • c) := by
      rw [Cold.cold_coarse_cube_open R a,
        Cold.cold_coarse_cube_open R (σ⁻¹ • c)]
      exact coarseBlockMatrix_congr_of_ae_eq hfieldR
    have hEllR := hEllCcube.mono (measurableSet_cubeSet R)
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hframe := Cold.cold_coarse_frame M.nu_pos hEllR hσ
    exact hcoarse.trans hframe
  have hlocalFrame : lemmaVInverseDepthMax Q a jj =
      σ * lemmaVInverseDepthMax Q c jj :=
    pureFlux_inverseDepthMax_frame_eq Q c a hEllCopen hEllA hσ jj hmatrix
  have hcoeff : attenuatedCoefficient M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω = c := by
    dsimp [c]
    calc
      _ = (Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun :=
        bank_one_pass_partial_coefficient M m 1 (by norm_num) t ω
      _ = _ := by rw [show m + (1 : ℤ) - 1 = m by omega]
  have hsourceMax : bankFiniteRootResponseMax (descendantsAtDepth Q jj)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (σ * lemmaVInverseDepthMax Q c jj) :=
    bank_depth_max_physical Q M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω c hcoeff hEllCopen jj
  let f : TriadicCube 2 → ℝ := fun R =>
    rootInverseResponse M R m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω
  have hsub (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q jj) : R ∈ D := by
    unfold D bankObserverDepthRootUnion
    refine Finset.mem_biUnion.mpr ⟨5, by norm_num, ?_⟩
    unfold bankObserverDepthRoots
    have hRroot := mem_descendantsAtDepth_add hQroot hR
    rw [hsj] at hRroot
    simpa using hRroot
  have hDnonempty : D.Nonempty := by
    obtain ⟨R, hR⟩ := descendantsAtDepth_nonempty Q jj
    exact ⟨R, hsub R hR⟩
  have hsourceSupEq : bankFiniteRootResponseMax (descendantsAtDepth Q jj)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (Book.Ch02.finsetSupReal (descendantsAtDepth Q jj) f) := by
    simpa [f] using obs_bank_response_max_eq_finsetSup
      (descendantsAtDepth Q jj) (descendantsAtDepth_nonempty Q jj)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω
  have hglobalSupEq : bankFiniteRootResponseMax D M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (Book.Ch02.finsetSupReal D f) := by
    simpa [f] using obs_bank_response_max_eq_finsetSup D hDnonempty
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω
  have hsup : Book.Ch02.finsetSupReal (descendantsAtDepth Q jj) f ≤
      Book.Ch02.finsetSupReal D f := by
    apply Book.Ch02.finsetSupReal_le (descendantsAtDepth Q jj)
      (descendantsAtDepth_nonempty Q jj)
    intro R hR
    exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
      D f (hsub R hR)
  have hmax : bankFiniteRootResponseMax (descendantsAtDepth Q jj)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω ≤
        bankFiniteRootResponseMax D M m (m + 40)
          (bankPartialInsertionWeights m 1 t) ω := by
    rw [hsourceSupEq, hglobalSupEq]
    exact ENNReal.ofReal_le_ofReal hsup
  have hYlt : bankFiniteRootResponseMax D M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω < ⊤ := by
    rw [hglobalSupEq]
    exact ENNReal.ofReal_lt_top
  have hreal := ENNReal.toReal_mono hYlt.ne hmax
  have hphysical0 : 0 ≤ σ * lemmaVInverseDepthMax Q c jj :=
    mul_nonneg hσ.le (lemmaVInverseDepthMax_nonneg Q c jj)
  rw [hsourceMax, ENNReal.toReal_ofReal hphysical0] at hreal
  have hglobal : lemmaVInverseDepthMax Q a jj ≤ Y := by
    rw [hlocalFrame]
    simpa [Y] using hreal
  have hsplit : Y ≤ inverseBankDepthA .localInverse M j +
      inverseBankDepthSlack M j + mixedOldLocalDepthRemainder M m t j ω := by
    dsimp [Y, mixedOldLocalDepthRemainder, inverseBankDepthBlockRemainder]
    exact (positive_split _ _ _).2
  have hprofile := (inverse_bank_depth_profile_bounds .localInverse M j).1
  have hbound : Y ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
      mixedOldLocalDepthRemainder M m t j ω := by
    calc
      Y ≤ inverseBankDepthA .localInverse M j + inverseBankDepthSlack M j +
          mixedOldLocalDepthRemainder M m t j ω := hsplit
      _ ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
          mixedOldLocalDepthRemainder M m t j ω := by
        nlinarith [hprofile]
  calc
    lemmaVInverseDepthMax Q a jj ≤ Y := hglobal
    _ ≤ mixedOldDepthCoefficient M m t j ω := by
      simpa [Y, mixedOldDepthCoefficient] using hbound


end
end ASDExplicitGamma.Main
