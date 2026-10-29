/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenResetTransport
public import ASDExplicitGamma.Inverse.BankResponseMeasurable
public import ASDExplicitGamma.Response.ResponseRealization
public import ASDExplicitGamma.Variational.LemmaVH1
public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine

/-! # Joint measurability along finite-even CIR insertion paths -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian
open Homogenization.Book

namespace ASDExplicitGamma.AllOrder

local instance cirJointMeasParentCompact (n : ℤ) :
    CompactSpace (closure (cubeSet (originCube 2 n))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure

abbrev CIRPathSample := (Set.Icc (0 : ℝ) 1) × Cutoff.CutoffSample 2

/-- The actual partial-insertion coefficient is jointly measurable in heat
time and sample.  The subtype keeps the elliptic path on its natural interval. -/
theorem aoCir_partialInsertedCoefficient_joint_measurable
    (M : ABKModel 2) (N : ℤ) :
    Measurable (fun z : CIRPathSample =>
      Model.partialInsertedCoefficient M (N - 1) z.1.1 z.2) := by
  refine Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro x i j
    have hbase : Measurable (fun z : CIRPathSample =>
        Cutoff.coefficientCutoff M.nu (N - 1) z.2 x i j) :=
      ((measurable_apply_entry x i j).comp
        (Cutoff.measurable_coefficientCutoff M.nu (N - 1))).comp measurable_snd
    have hsqrt : Measurable (fun z : CIRPathSample => Real.sqrt z.1.1) :=
      Real.continuous_sqrt.measurable.comp
        (continuous_subtype_val.measurable.comp measurable_fst)
    have hfresh : Measurable (fun z : CIRPathSample =>
        ShellField.forgetShell (z.2.1 (N - 1 + 1)) x i j) := by
      exact ((measurable_apply_entry x i j).comp ShellField.measurable_forgetShell).comp
        ((measurable_pi_apply (N - 1 + 1)).comp
          (measurable_subtype_coe.comp measurable_snd))
    change Measurable (fun z : CIRPathSample =>
      Cutoff.coefficientCutoff M.nu (N - 1) z.2 x i j +
        Real.sqrt z.1.1 * ShellField.forgetShell (z.2.1 (N - 1 + 1)) x i j)
    exact hbase.add (hsqrt.mul hfresh)
  · intro i j φ hφ
    have hbase : Measurable (fun z : CIRPathSample =>
        entryTestR i j φ (Cutoff.coefficientCutoff M.nu (N - 1) z.2)) :=
      (measurable_entryTestR i j hφ).comp
        ((Cutoff.measurable_coefficientCutoff M.nu (N - 1)).comp measurable_snd)
    have hsqrt : Measurable (fun z : CIRPathSample => Real.sqrt z.1.1) :=
      Real.continuous_sqrt.measurable.comp
        (continuous_subtype_val.measurable.comp measurable_fst)
    have hfresh : Measurable (fun z : CIRPathSample =>
        entryTestR i j φ (ShellField.forgetShell (z.2.1 (N - 1 + 1)))) :=
      (measurable_entryTestR i j hφ).comp
        (ShellField.measurable_forgetShell.comp
          ((measurable_pi_apply (N - 1 + 1)).comp
            (measurable_subtype_coe.comp measurable_snd)))
    have heq : (fun z : CIRPathSample => entryTestR i j φ
        (Model.partialInsertedCoefficient M (N - 1) z.1.1 z.2)) =
        fun z => entryTestR i j φ (Cutoff.coefficientCutoff M.nu (N - 1) z.2) +
          Real.sqrt z.1.1 * entryTestR i j φ
            (ShellField.forgetShell (z.2.1 (N - 1 + 1))) := by
      funext z
      unfold Model.partialInsertedCoefficient
      rw [entryTestR_add i j hφ,
        entryTestR_smul i j (Real.sqrt z.1.1)
          (ShellField.forgetShell (z.2.1 (N - 1 + 1)))]
    rw [heq]
    exact hbase.add (hsqrt.mul hfresh)

/-- Every value of the path is locally uniformly elliptic, with constants
allowed to depend on the compact observation cube and the sample. -/
private theorem aoCir_partialInserted_locallyElliptic
    (M : ABKModel 2) (N : ℤ) (z : CIRPathSample) :
    Book.Ch04.AELocallyUniformlyEllipticField
      (Model.partialInsertedCoefficient M (N - 1) z.1.1 z.2) := by
  intro Q
  let K := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨ell, hcover⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact hK
  have hcover' : ∀ x ∈ cubeSet Q,
      x ∈ openCubeSet (originCube 2 (ell : ℤ)) := fun x hx => hcover (subset_closure hx)
  have ht : 0 ≤ z.1.1 ∧ z.1.1 ≤ 1 := z.1.2
  let Λ : ℝ := ((2 : ℝ) * 2 *
      (Model.partialInsertedEntryBound M (ell : ℤ) (N - 1) z.2) ^ 2 + M.nu ^ 2) / M.nu
  have hEll : IsEllipticFieldOn M.nu Λ (cubeSet Q)
      (Model.partialInsertedCoefficient M (N - 1) z.1.1 z.2).toFun := by
    simpa only [Λ] using Model.partialInsertedCoefficient_isEllipticFieldOn
      M (ell : ℤ) (N - 1) z.2 ht (measurableSet_cubeSet Q) hcover'
  have hOpen := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  obtain ⟨x, hx⟩ := Book.Ch02.openCubeSet_nonempty Q
  exact ⟨M.nu, Λ, M.nu_pos, (hOpen.2 x hx).2.1,
    IsAEEllipticFieldOn.of_isEllipticFieldOn hOpen⟩

/-- The reset trace of a one-shell inserted coefficient is jointly measurable. -/
theorem aoCir_step_rootTrace_joint_measurable
    (M : ABKModel 2) (Q : TriadicCube 2) (base N K₀ : ℤ) (hbase : base < N) :
    Measurable (fun z : CIRPathSample =>
      rootTraceObservable M Q base N K₀ (aoCirStepWeights N z.1.1) z.2) := by
  let X : CIRPathSample → RegCoeffField 2 :=
    fun z => Model.partialInsertedCoefficient M (N - 1) z.1.1 z.2
  have hX : Measurable X := by
    simpa only [X] using aoCir_partialInsertedCoefficient_joint_measurable M N
  have hEll : ∀ z, Book.Ch04.AELocallyUniformlyEllipticField (X z) :=
    fun z => aoCir_partialInserted_locallyElliptic M N z
  have hUL := Provider.BadEvents.measurable_comp_coarseB_cubeSet hX hEll Q
  have hLR := Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet hX hEll Q
  have htraceUL : Measurable (fun z : CIRPathSample =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) (X z).toFun).upperLeft) := by
    change Measurable (fun z => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X z).toFun).upperLeft i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
  have htraceLR : Measurable (fun z : CIRPathSample =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) (X z).toFun).lowerRight) := by
    change Measurable (fun z => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X z).toFun).lowerRight i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
  have hcoeff (z : CIRPathSample) :
      attenuatedCoefficient M base N (aoCirStepWeights N z.1.1) z.2 = (X z).toFun := by
    funext x
    rw [aoCir_step_coefficient M base N hbase z.1.1 z.2 x]
  have heq : (fun z : CIRPathSample =>
      rootTraceObservable M Q base N K₀ (aoCirStepWeights N z.1.1) z.2) =
      fun z => (Annealed.sigmaBar M K₀ : ℝ)⁻¹ *
          Matrix.trace (coarseBlockMatrix (cubeSet Q) (X z).toFun).upperLeft +
        (Annealed.sigmaBar M K₀ : ℝ) *
          Matrix.trace (coarseBlockMatrix (cubeSet Q) (X z).toFun).lowerRight := by
    funext z
    rw [root_trace_observable_eq_trace_defect]
    simp only [traceDefect, hcoeff z]
    ring
  rw [heq]
  exact (htraceUL.const_mul _).add (htraceLR.const_mul _)

/-- The reset inverse-root observable of a one-shell path is jointly measurable. -/
theorem aoCir_step_rootInverse_joint_measurable
    (M : ABKModel 2) (Q : TriadicCube 2) (base N K₀ : ℤ) (hbase : base < N) :
    Measurable (fun z : CIRPathSample =>
      rootInverseObservable M Q base N K₀ (aoCirStepWeights N z.1.1) z.2) := by
  let X : CIRPathSample → RegCoeffField 2 :=
    fun z => Model.partialInsertedCoefficient M (N - 1) z.1.1 z.2
  have hX : Measurable X := by
    simpa only [X] using aoCir_partialInsertedCoefficient_joint_measurable M N
  have hEll : ∀ z, Book.Ch04.AELocallyUniformlyEllipticField (X z) :=
    fun z => aoCir_partialInserted_locallyElliptic M N z
  have hLR := Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet hX hEll Q
  let L : Mat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
    { toFun := fun A => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) A B
      map_smul' := fun c A => map_smul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) c A }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hnorm : Measurable (fun z : CIRPathSample =>
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        ((coarseBlockMatrix (cubeSet Q) (X z).toFun).lowerRight)‖) :=
    hL.norm.measurable.comp hLR
  have hcoeff (z : CIRPathSample) :
      attenuatedCoefficient M base N (aoCirStepWeights N z.1.1) z.2 = (X z).toFun := by
    funext x
    rw [aoCir_step_coefficient M base N hbase z.1.1 z.2 x]
  have heq : (fun z : CIRPathSample =>
      rootInverseObservable M Q base N K₀ (aoCirStepWeights N z.1.1) z.2) =
      fun z => (Annealed.sigmaBar M K₀ : ℝ) *
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          ((coarseBlockMatrix (cubeSet Q) (X z).toFun).lowerRight)‖ := by
    funext z
    simp only [rootInverseObservable, hcoeff z]
  rw [heq]
  exact hnorm.const_mul _

private theorem aoCir_reset_tile_depth_joint_measurable
    (M : ABKModel 2) (Q U : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (j d : ℕ)
    (hU : U ∈ descendantsAtDepth Q j) :
    Measurable (fun z : CIRPathSample => lemmaVInverseDepthMax U
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N z.1.1 z.2)) d) := by
  classical
  let S := descendantsAtDepth U d
  have hS : S.Nonempty := descendantsAtDepth_nonempty U d
  have hroot (R : TriadicCube 2) (hR : R ∈ S) :
      Measurable (fun z : CIRPathSample => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand 48)) N Q.scale
        (aoCirStepWeights N z.1.1) z.2) := by
    have hRglobal : R ∈ descendantsAtDepth Q (j + d) :=
      mem_descendantsAtDepth_add hU hR
    have hOld : protectedOldLabel R.scale (orderBand 48) < N := by
      simp only [protectedOldLabel]
      have hs := scale_eq_sub_of_mem_descendantsAtDepth hRglobal
      omega
    exact aoCir_step_rootInverse_joint_measurable M R
      (protectedOldLabel R.scale (orderBand 48)) N Q.scale hOld
  have hpoint (z : CIRPathSample) :
      Book.Ch02.finsetSupReal S (fun R => Book.Ch02.matrixNorm
          (sigmaStarInvCoarse (openCubeSet R)
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M Q.scale : ℝ)
              (aoCirInsertedResponseCoefficient Q n hQ N z.1.1 z.2)))) =
        Book.Ch02.finsetSupReal S (fun R => rootInverseObservable M R
          (protectedOldLabel R.scale (orderBand 48)) N Q.scale
          (aoCirStepWeights N z.1.1) z.2) := by
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    have hRglobal : R ∈ descendantsAtDepth Q (j + d) :=
      mem_descendantsAtDepth_add hU hR
    exact (aoCir_step_inverse_cell_eq_responseFrame_norm M Q R n ell hQ hK N hN
      48 z.1.1 (j + d) hRglobal z.2).symm
  have heq : (fun z : CIRPathSample => lemmaVInverseDepthMax U
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N z.1.1 z.2)) d) =
      S.sup' hS (fun R z => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand 48)) N Q.scale
        (aoCirStepWeights N z.1.1) z.2) := by
    funext z
    change Book.Ch02.finsetSupReal S _ = _
    simpa only [Finset.sup'_apply,
      ← Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS] using hpoint z
  rw [heq]
  exact Finset.measurable_sup' hS (fun R hR => hroot R hR)

/-- The complete depth-four inverse tile history is jointly measurable along
the insertion path. -/
theorem aoCir_step_tile_history_joint_measurable
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (j : ℕ) :
    Measurable (fun z : CIRPathSample => pureFluxSourceTileHistory Q j
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N z.1.1 z.2))) := by
  classical
  let S := descendantsAtDepth Q j
  have hS : S.Nonempty := descendantsAtDepth_nonempty Q j
  let a (z : CIRPathSample) := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M Q.scale : ℝ)
    (aoCirInsertedResponseCoefficient Q n hQ N z.1.1 z.2)
  let r : ℝ := ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹
  have hterm (U : TriadicCube 2) (hU : U ∈ S) (d : ℕ) :
      Measurable (fun z : CIRPathSample => r ^ d * lemmaVInverseDepthMax U (a z) d) :=
    measurable_const.mul (aoCir_reset_tile_depth_joint_measurable M Q U n ell hQ hK
      N hN j d hU)
  have hhistory (U : TriadicCube 2) (hU : U ∈ S) :
      Measurable (fun z : CIRPathSample =>
        lemmaVInverseHistory U (a z) ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    change Measurable (fun z => (1 - r) *
      ∑' d : ℕ, r ^ d * lemmaVInverseDepthMax U (a z) d)
    exact measurable_const.mul (Measurable.tsum (hterm U hU))
  have hsup : Measurable (S.sup' hS fun U z =>
      lemmaVInverseHistory U (a z) ((3 : ℝ) ^ (1 / 4 : ℝ))) :=
    Finset.measurable_sup' hS (fun U hU => hhistory U hU)
  have heq : (fun z : CIRPathSample => pureFluxSourceTileHistory Q j (a z)) =
      S.sup' hS (fun U z => lemmaVInverseHistory U (a z)
        ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    funext z
    change Book.Ch02.finsetSupReal S _ = _
    rw [Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS]
    simp only [Finset.sup'_apply]
  rw [heq]
  exact hsup

/-- The actual finite-family CIR history load is jointly measurable in time
and sample. -/
theorem aoCir_reset_square_family_load_joint_measurable
    {ι : Type*} (M : ABKModel 2) (frameLabel n ell N : ℤ)
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2)
    (hQ : ∀ a, closure (openCubeSet (Q a)) ⊆
      closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆
      openCubeSet (originCube 2 ell))
    (hscale : ∀ a ∈ s, (Q a).scale = frameLabel)
    (hN : frameLabel ≤ N) (hw : ∀ a ∈ s, 0 ≤ w a)
    (hsum : ∑ a ∈ s, w a = 1) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Measurable (fun z : CIRPathSample => cirFamilyHistoryLoad
      (cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L
        (fun a t ω => cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) t ω))
        hw hsum) z.1.1 z.2) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let k : (a : ι) → ℝ → Cutoff.CutoffSample 2 →
      ResponseCoefficient (openCubeSet (Q a)) := fun a t ω =>
    cirSquareRestrictionCLM (Q a) (hQ a) (modelInsertedScalar K (N - 1) t ω)
  let F := cirSquareResponseFamily s w Q (fun _ => 4) M frameLabel b L k hw hsum
  have hQscale (a : ι) (ha : a ∈ s) : (Q a).scale ≤ N := by
    rw [hscale a ha]
    exact hN
  have htrace (a : ι) (ha : a ∈ s) :
      Measurable (fun z : CIRPathSample => F.trace a z.1.1 z.2) := by
    let old := protectedOldLabel (Q a).scale (orderBand (4 : ℝ))
    have hOld : old < N := by
      dsimp [old, protectedOldLabel]
      rw [hscale a ha]
      omega
    have hroot := aoCir_step_rootTrace_joint_measurable
      M (Q a) old N frameLabel hOld
    have heq (z : CIRPathSample) : rootTraceObservable M (Q a) old N
        frameLabel (aoCirStepWeights N z.1.1) z.2 = F.trace a z.1.1 z.2 + 4 := by
      have he := aoCir_step_trace_eq_squareTrace M (Q a) n ell
        (hQ a) hK old N frameLabel hOld z.1.1 z.2
      change rootTraceObservable M (Q a) old N frameLabel
          (aoCirStepWeights N z.1.1) z.2 =
        squareTrace (Q a) M.nu (Annealed.sigmaBar M frameLabel : ℝ)
          (cirSquareRestrictionCLM (Q a) (hQ a)
            (modelInsertedScalar K (N - 1) z.1.1 z.2)) + 4
      exact he
    have htraceEq : (fun z : CIRPathSample => F.trace a z.1.1 z.2) =
        fun z => rootTraceObservable M (Q a) old N frameLabel
          (aoCirStepWeights N z.1.1) z.2 - 4 := by
      funext z
      linarith [heq z]
    rw [htraceEq]
    exact hroot.sub_const 4
  have hhistory (a : ι) (ha : a ∈ s) :
      Measurable (fun z : CIRPathSample => F.inverseHistory a z.1.1 z.2) := by
    have h := aoCir_step_tile_history_joint_measurable M (Q a) n ell
      (hQ a) hK N (hQscale a ha) 4
    have heq : (fun z : CIRPathSample => F.inverseHistory a z.1.1 z.2) =
        fun z => pureFluxSourceTileHistory (Q a) 4
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M (Q a).scale : ℝ)
            (aoCirInsertedResponseCoefficient (Q a) n (hQ a) N z.1.1 z.2)) := by
      funext z
      change pureFluxSourceTileHistory (Q a) 4
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M frameLabel : ℝ)
            (cirSquareRestrictionCLM (Q a) (hQ a)
              (modelInsertedScalar K (N - 1) z.1.1 z.2))) = _
      rw [hscale a ha]
      rfl
    rw [heq]
    exact h
  change Measurable (fun z : CIRPathSample => ∑ a ∈ s,
    w a * F.inverseHistory a z.1.1 z.2 ^ 2 * (F.trace a z.1.1 z.2 + 4))
  apply Finset.measurable_sum
  intro a ha
  exact (measurable_const.mul ((hhistory a ha).pow_const 2)).mul
    ((htrace a ha).add measurable_const)

end ASDExplicitGamma.AllOrder
