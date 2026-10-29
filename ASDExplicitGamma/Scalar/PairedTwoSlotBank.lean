module

public import ASDExplicitGamma.Scalar.FlatResolventSourceBridge
public import ASDExplicitGamma.Scalar.PairedTwoSlotBound

/-! The cell inverse histories of the physical NEW coefficient are bounded by the global
NEW bank, and the resulting NEW two-slot bound. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
  ASDExplicitGamma.Response ASDExplicitGamma.Model ASDExplicitGamma.Inverse
  ASDExplicitGamma.Variational
open Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

local instance bankClosedCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

theorem bank_cubeSet_subset_closure_openCubeSet (Q : TriadicCube 2) :
    cubeSet Q ⊆ closure (openCubeSet Q) := by
  rw [cubeSet_eq_pi_Ico]
  intro x hx
  rw [openCubeSet_eq_pi_Ioo, closure_pi_set]
  intro i hi
  have hxi := hx i (by simp)
  have hne :
      ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) ≠
        (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) := by
    have hscale := ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q
    nlinarith
  change x i ∈ closure (Set.Ioo
    ((((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q))
    ((((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)))
  rw [closure_Ioo hne]
  exact ⟨hxi.1, le_of_lt hxi.2⟩
theorem partial_insertion_frame_history_eq_cell
    (Q U : TriadicCube 2) (n : ℕ) (hU : U ∈ descendantsAtDepth Q n) (M : ABKModel 2) (ell m : ℤ)
    (ω : Cutoff.CutoffSample 2) (σ : ℝ) (hσ : 0 < σ)
    (K : Set (Vec 2)) [CompactSpace K]
    (hQ : closure (openCubeSet Q) ⊆ K)
    (hK : K ⊆ openCubeSet (originCube 2 ell)) :
    let k := physicalResponseRestriction Q
      hQ (modelInsertedScalar K m 1 ω)
    lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) =
      σ * lemmaVInverseHistory U
        (Model.partialInsertedCoefficient M m 1 ω).toFun
        ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
  let hQopen : closure (openCubeSet Q) ⊆ K := hQ
  have hUopen : openCubeSet U ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hUcube : cubeSet U ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hU
  have hQcube : closure (cubeSet Q) ⊆ K := by
    calc
      closure (cubeSet Q) ⊆ closure (closure (openCubeSet Q)) :=
        closure_mono (bank_cubeSet_subset_closure_openCubeSet Q)
      _ = closure (openCubeSet Q) := closure_closure
      _ ⊆ K := hQ
  let f := modelInsertedScalar K m 1 ω
  let k := physicalResponseRestriction Q hQopen f
  let a := (Model.partialInsertedCoefficient M m 1 ω).toFun
  let af := responseFramePlanarCoefficientField M.nu σ k
  have hEll : IsEllipticFieldOn M.nu
      (((2 : ℝ) * (2 : ℝ) *
        (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (openCubeSet U) a := by
    simpa [a] using Model.partialInsertedCoefficient_isEllipticFieldOn
      M ell m ω (t := 1) ⟨by norm_num, by norm_num⟩
      (measurableSet_openCubeSet U) (fun _ hx => hK (hQ (subset_closure (hUopen hx))))
  have hEllFrame := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k).mono (measurableSet_openCubeSet U) hUopen
  have hMatrix (R : TriadicCube 2) (d : ℕ)
      (hR : R ∈ descendantsAtDepth U d) :
      coarseBlockMatrix (cubeSet R) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) a) := by
    have hRQ : cubeSet R ⊆ cubeSet Q :=
      (cubeSet_subset_of_mem_descendantsAtDepth hR).trans hUcube
    have hRK : closure (cubeSet R) ⊆ K := (closure_mono hRQ).trans hQcube
    have hRKopen : closure (openCubeSet R) ⊆ K :=
      (closure_mono (openCubeSet_subset_cubeSet R)).trans hRK
    let incl : C(closure (cubeSet R), K) :=
      ⟨fun x => ⟨x.1, hRK x.2⟩, by fun_prop⟩
    let kR : ResponseCoefficient (cubeSet R) :=
      (ContinuousMap.linearIsometryBoundedOfCompact
          (closure (cubeSet R)) ℝ ℝ).toLinearIsometry.toContinuousLinearMap.comp
        (ContinuousMap.compCLM ℝ ℝ incl) f
    have hkR (x : Vec 2) (hx : x ∈ cubeSet R) :
        responseCoefficientExtension kR x = f ⟨x, hRK (subset_closure hx)⟩ := by
      rw [responseCoefficientExtension_eq kR hx]
      change f ⟨x, hRK (subset_closure hx)⟩ = _
      rfl
    have hframeAE : af =ᵐ[MeasureTheory.volume.restrict (openCubeSet R)]
        responseFramePlanarCoefficientField M.nu σ kR := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      have hxQ : x ∈ openCubeSet Q :=
        hUopen (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)
      change responseFramePlanarCoefficientField M.nu σ k x =
        responseFramePlanarCoefficientField M.nu σ kR x
      rw [responseFramePlanarCoefficientField_apply,
        responseFramePlanarCoefficientField_apply,
        responseCoefficientExtension_eq k hxQ,
        hkR x (openCubeSet_subset_cubeSet R hx)]
      rfl
    have hplainAE : responsePlanarCoefficientField M.nu kR =ᵐ[
        MeasureTheory.volume.restrict (openCubeSet R)] a := by
      filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      have hresponse := physical_response_coefficient_eq_actual
        R hRKopen
        M ell m hK 1 ω x hx
      change responsePlanarCoefficient M.nu
        (responseCoefficientExtension
          (physicalResponseRestriction R hRKopen f) x) = a x
        at hresponse
      have hsame : responseCoefficientExtension kR x =
          responseCoefficientExtension
            (physicalResponseRestriction R hRKopen f) x := by
        rw [hkR x (openCubeSet_subset_cubeSet R hx),
          responseCoefficientExtension_eq
            (physicalResponseRestriction R hRKopen f) hx]
        rfl
      change responsePlanarCoefficient M.nu (responseCoefficientExtension kR x) = a x
      rw [hsame]
      exact hresponse
    have hframeMatrix := response_coarseMatrix_frame_eq
      (measurableSet_cubeSet R) M.nu σ M.nu_pos hσ kR
    have hframeMatrix' : coarseBlockMatrix (cubeSet R) af =
        coarseBlockMatrix (cubeSet R)
          (responseFramePlanarCoefficientField M.nu σ kR) := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
      exact coarseBlockMatrix_congr_of_ae_eq hframeAE
    have hplainMatrix : coarseBlockMatrix (cubeSet R)
        (responsePlanarCoefficientField M.nu kR) =
          coarseBlockMatrix (cubeSet R) a := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
      exact coarseBlockMatrix_congr_of_ae_eq hplainAE
    calc
      coarseBlockMatrix (cubeSet R) af =
          coarseBlockMatrix (cubeSet R)
            (responseFramePlanarCoefficientField M.nu σ kR) := hframeMatrix'
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu kR)) := hframeMatrix
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet R) a) :=
        congrArg (frameMatrix σ) hplainMatrix
  exact pureFlux_inverseHistory_frame_eq U a af hEll hEllFrame hσ hMatrix

/-- **Two-slot NEW inverse bound.**  For the paired source `s = (Π_flux F, Π_X G)` the
`J`-form of the actual NEW inverse is bounded by `(44/25)` times the volume, the bank cap
of the cell inverse histories, and the tiled positive-Haar energies of the two source
fields. -/
theorem paired_two_slot_new_inverse_bound (Q : TriadicCube 2) (n : ℕ) {ν σ : ℝ}
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hFc : ∀ U ∈ descendantsAtDepth Q n, MemLp F 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => F x i))))
    (hGc : ∀ U ∈ descendantsAtDepth Q n, MemLp G 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => G x i))))
    {Bstar : ℝ}
    (hB : ∀ U ∈ descendantsAtDepth Q n, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ Bstar) :
    ⟪pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule)
        (WithLp.toLp 2 (fluxSource Q hF, potSource Q hG)),
      pureFluxBlockInverse (Y := HilbertVectorL2 (openCubeSet Q))
        (X := (physicalPotentialSpace Q).toSubmodule) (ν / σ) (div_pos hν hσ)
        (physicalProjectedCoefficient Q σ hσ k)
        (WithLp.toLp 2 (fluxSource Q hF, potSource Q hG))⟫_ℝ ≤
      (44 / 25 : ℝ) * ((volume (openCubeSet Q)).toReal *
        (Bstar * (lemmaVTiledPositiveEnergy Q n F + lemmaVTiledPositiveEnergy Q n G))) := by
  rw [twoSlot_J]
  exact two_slot_bound_core Q n hν hσ k hF hG hFc hGc (fluxSource Q hF)
    (potSource Q hG) (fluxSource_mem Q hF) (fluxSource_inner Q hF)
    (potSource_inner Q hG) hB

end

end ASDExplicitGamma.Scalar
