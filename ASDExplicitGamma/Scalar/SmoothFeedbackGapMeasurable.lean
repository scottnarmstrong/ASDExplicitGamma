/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import ASDExplicitGamma.Scalar.UpperCellEnergyMeasurability
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapPair
public import ASDExplicitGamma.Scalar.SmoothFeedbackJointCell

/-! Measurability in the OLD sample of the actual gap `Gap`: the energy and the
source pairing are continuous functionals on the Hilbert carrier, the
energy bilinear forms depend measurably on the sample, and the maximal value
is a countable supremum over a dense sequence of genuine variations. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- The plain pairing with a fixed first-block load, as a continuous linear
functional on the Hilbert carrier. -/
noncomputable def pairingCLM (U : Set (Vec 2)) {w : Vec 2 → Vec 2}
    (hw : MemVectorL2 U w) : HilbertBlockL2 U →L[ℝ] ℝ :=
  ((MeasureTheory.volume U).toReal)⁻¹ •
    ((innerSL ℝ (toHilbertVectorL2OfVecField hw)).comp
      (hilbertBlockL2PotentialCLM (U := U)))

theorem pairingCLM_eq {U : Set (Vec 2)} {w : Vec 2 → Vec 2}
    (hw : MemVectorL2 U w) {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 U F) :
    pairingCLM U hw (toHilbertBlockL2OfBlockField hF) =
      scalarSourcePairing U w F := by
  unfold pairingCLM scalarSourcePairing volumeAverage
  have hF1 : MemVectorL2 U (fun x => (F x).1) := memVectorL2_fst_of_memBlockL2 hF
  have hpot : hilbertBlockL2PotentialCLM (U := U) (toHilbertBlockL2OfBlockField hF) =
      toHilbertVectorL2OfVecField hF1 := by
    apply Lp.ext
    filter_upwards [coeFn_hilbertBlockL2PotentialCLM (U := U) (toHilbertBlockL2OfBlockField hF),
      coeFn_toHilbertBlockL2OfBlockField (U := U) hF,
      coeFn_toHilbertVectorL2OfVecField (U := U) hF1] with x h1 h2 h3
    rw [h1, h3]
    rw [h2]
    first | rfl | simp [hilbertifyBlockField, hilbertifyVecField, HilbertBlockVec.potential]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  rw [hpot, inner_toHilbertVectorL2OfVecField_eq_integral]

/-- The maximal value of a family of strictly concave quadratic functionals,
attained on a subset of a separable Hilbert space, is measurable in the
parameter when the quadratic forms are. -/
theorem maximal_value_measurable
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    [MeasurableSpace (E →L[ℝ] E →L[ℝ] ℝ)]
    (B : Ω → E →L[ℝ] E →L[ℝ] ℝ) (hB : Measurable B)
    (hev : ∀ T : E, Measurable fun ω => B ω T T)
    (ℓ : E →L[ℝ] ℝ) (S : Set E) (Z : Ω → E)
    (hZS : ∀ ω, Z ω ∈ S)
    (hmax : ∀ ω, ∀ T ∈ S, 2 * ℓ T - B ω T T ≤ 2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) :
    Measurable fun ω => 2 * ℓ (Z ω) - B ω (Z ω) (Z ω) := by
  classical
  obtain ⟨t, htS, htc, hSt⟩ := (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  haveI : Countable t := htc.to_subtype
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · exact measurable_of_empty _
  haveI : Nonempty t := by
    obtain ⟨T, hT⟩ : t.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := hSt (hZS ω₀)
      rw [h, closure_empty] at this
      exact this
    exact ⟨⟨T, hT⟩⟩
  have hf (T : E) : Measurable fun ω => 2 * ℓ T - B ω T T :=
    measurable_const.sub (hev T)
  have hsup : Measurable fun ω => ⨆ T : t, (2 * ℓ T.1 - B ω T.1 T.1) :=
    Measurable.iSup fun T => hf T.1
  have heq : (fun ω => 2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) =
      fun ω => ⨆ T : t, (2 * ℓ T.1 - B ω T.1 T.1) := by
    funext ω
    have hbdd : BddAbove (Set.range fun T : t => 2 * ℓ T.1 - B ω T.1 T.1) :=
      ⟨2 * ℓ (Z ω) - B ω (Z ω) (Z ω), by
        rintro _ ⟨T, rfl⟩
        exact hmax ω T.1 (htS T.2)⟩
    apply le_antisymm
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hcont : Continuous fun T : E => 2 * ℓ T - B ω T T :=
        (continuous_const.mul ℓ.continuous).sub
          ((B ω).continuous.clm_apply continuous_id)
      have hopen : IsOpen {T : E | 2 * ℓ (Z ω) - B ω (Z ω) (Z ω) - ε <
          2 * ℓ T - B ω T T} :=
        isOpen_lt continuous_const hcont
      have hmem : Z ω ∈ {T : E | 2 * ℓ (Z ω) - B ω (Z ω) (Z ω) - ε <
          2 * ℓ T - B ω T T} := by
        change _ < _
        linarith
      obtain ⟨T, hTo, hTt⟩ := mem_closure_iff.mp (hSt (hZS ω)) _ hopen hmem
      have hle : 2 * ℓ T - B ω T T ≤ ⨆ T : t, (2 * ℓ T.1 - B ω T.1 T.1) :=
        le_ciSup hbdd ⟨T, hTt⟩
      have hT : 2 * ℓ (Z ω) - B ω (Z ω) (Z ω) - ε < 2 * ℓ T - B ω T T := hTo
      linarith
    · exact ciSup_le fun T => hmax ω T.1 (htS T.2)
  rw [heq]
  exact hsup

/-- The source energy is the Hilbert quadratic form of the realization. -/
theorem scalar_field_energy_eq_bilin
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) :
    scalarFieldEnergy ν σ k F =
      (scalarFrameRealization Q ν σ hν hσ k).energyBilin
        (toHilbertBlockL2OfBlockField hF) (toHilbertBlockL2OfBlockField hF) := by
  rw [scalar_frame_bilinear_field Q ν σ hν hσ k hF hF]
  unfold scalarFieldEnergy
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ
    (responseCoefficientExtension k x) hν hσ]
  rfl

/-- Measurability of the energy of the actual OLD maximizer. -/
theorem smooth_feedback_maximizer_energy_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2)
    (hZ : ∀ ω, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) w (Z ω)) :
    Measurable fun ω => scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (Z ω) := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  let hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  let B : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q) →L[ℝ]
      HilbertBlockL2 (openCubeSet Q) →L[ℝ] ℝ := fun ω =>
    (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
      (oldCutoffSkewCoefficient m Q ω)).energyBilin
  have hB : Measurable B :=
    measurable_oldCutoff_scalarFrameEnergyBilin m Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ
  have hev (T : HilbertBlockL2 (openCubeSet Q)) : Measurable fun ω => B ω T T :=
    (hB.clm_apply measurable_const).clm_apply measurable_const
  let ℓ := pairingCLM (openCubeSet Q) hw
  let S : Set (HilbertBlockL2 (openCubeSet Q)) :=
    {h | ∃ (Y : Vec 2 → BlockVec 2) (hY : ScalarVariation (openCubeSet Q) Y),
      h = toHilbertBlockL2OfBlockField hY.1}
  have hmeas := maximal_value_measurable B hB hev ℓ S
    (fun ω => toHilbertBlockL2OfBlockField (hZ ω).1.1)
    (fun ω => ⟨Z ω, (hZ ω).1, rfl⟩)
    (by
      intro ω T hT
      obtain ⟨Y, hY, rfl⟩ := hT
      have h1 := (hZ ω).2 Y hY
      have e1 : ℓ (toHilbertBlockL2OfBlockField hY.1) =
          scalarSourcePairing (openCubeSet Q) w Y := pairingCLM_eq hw hY.1
      have e2 : B ω (toHilbertBlockL2OfBlockField hY.1) (toHilbertBlockL2OfBlockField hY.1) =
          scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
            (oldCutoffSkewCoefficient m Q ω) Y :=
        (scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ _ hY.1).symm
      have e3 : ℓ (toHilbertBlockL2OfBlockField (hZ ω).1.1) =
          scalarSourcePairing (openCubeSet Q) w (Z ω) := pairingCLM_eq hw _
      have e4 : B ω (toHilbertBlockL2OfBlockField (hZ ω).1.1)
          (toHilbertBlockL2OfBlockField (hZ ω).1.1) =
          scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
            (oldCutoffSkewCoefficient m Q ω) (Z ω) :=
        (scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ _ (hZ ω).1.1).symm
      rw [e1, e2, e3, e4]
      exact h1)
  have heq : (fun ω => scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (Z ω)) = fun ω =>
      2 * ℓ (toHilbertBlockL2OfBlockField (hZ ω).1.1) -
        B ω (toHilbertBlockL2OfBlockField (hZ ω).1.1)
          (toHilbertBlockL2OfBlockField (hZ ω).1.1) := by
    funext ω
    have hid := scalar_old_maximizer_energy_identity Q M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) w (Z ω) (hZ ω)
    have e3 : ℓ (toHilbertBlockL2OfBlockField (hZ ω).1.1) =
        scalarSourcePairing (openCubeSet Q) w (Z ω) := pairingCLM_eq hw _
    have e4 : B ω (toHilbertBlockL2OfBlockField (hZ ω).1.1)
        (toHilbertBlockL2OfBlockField (hZ ω).1.1) =
        scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
          (oldCutoffSkewCoefficient m Q ω) (Z ω) :=
      (scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ _ (hZ ω).1.1).symm
    rw [e3, e4, hid]
    ring
  rw [heq]
  exact hmeas

theorem scalarFieldEnergy_eq_pairing
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2) :
    scalarFieldEnergy nu sigma k F = oldSignedEnergyPairing Q nu sigma k F F := by
  unfold scalarFieldEnergy oldSignedEnergyPairing
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock nu sigma
    (responseCoefficientExtension k x) hnu hsigma]
  rfl

/-- The energy and the source pairing of an actual OLD cell residual of a
fixed load are measurable in the OLD sample. -/
theorem cell_residual_functionals_measurable
    (m : ℤ) (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (w : Vec 2 → Vec 2) (hw : MemVectorL2 (openCubeSet U) w) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      oldSignedEnergyPairing U nu sigma
        (oldSignedCellCoefficient Q U hU (oldCutoffSkewCoefficient m Q ω))
        (oldSignedCellResidual Q U hU nu sigma hnu hsigma
          (oldCutoffSkewCoefficient m Q ω) F hF)
        (oldSignedCellResidual Q U hU nu sigma hnu hsigma
          (oldCutoffSkewCoefficient m Q ω) F hF)) ∧
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      scalarSourcePairing (openCubeSet U) w
        (oldSignedCellResidual Q U hU nu sigma hnu hsigma
          (oldCutoffSkewCoefficient m Q ω) F hF)) := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet U)) :=
    (isOpenBoundedConvexDomain_openCubeSet U).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet U)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet U)) := inferInstance
  let hFR : MemBlockL2 (openCubeSet U) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hU)
  let r : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet U) := fun ω =>
    scalarProjectionResidual U nu sigma hnu hsigma (oldCutoffSkewCoefficient m U ω)
      (toHilbertBlockL2OfBlockField hFR)
  have hr : Measurable r :=
    upper_cell_random_projection_measurable m U nu sigma hnu hsigma
      (fun _ => toHilbertBlockL2OfBlockField hFR) measurable_const
  have hk (ω : Cutoff.CutoffSample 2) :
      oldSignedCellCoefficient Q U hU (oldCutoffSkewCoefficient m Q ω) =
        oldCutoffSkewCoefficient m U ω :=
    smooth_feedback_cell_coefficient_restrict m Q U hU ω
  have hres (ω : Cutoff.CutoffSample 2) :
      toHilbertBlockL2OfBlockField
        (Lp.memLp (oldSignedCellResidual Q U hU nu sigma hnu hsigma
          (oldCutoffSkewCoefficient m Q ω) F hF)) = r ω := by
    have : oldSignedCellResidual Q U hU nu sigma hnu hsigma
        (oldCutoffSkewCoefficient m Q ω) F hF =
        scalarResidualField U nu sigma hnu hsigma (oldCutoffSkewCoefficient m U ω)
          (toHilbertBlockL2OfBlockField hFR) := by
      unfold oldSignedCellResidual
      simp only []
      rw [hk ω]
    rw [this]
    exact hilbert_field_rebuild _
  have hB : Measurable fun ω : Cutoff.CutoffSample 2 =>
      (scalarFrameRealization U nu sigma hnu hsigma
        (oldCutoffSkewCoefficient m U ω)).energyBilin :=
    measurable_oldCutoff_scalarFrameEnergyBilin m U nu sigma hnu hsigma
  constructor
  · have hm : Measurable fun ω : Cutoff.CutoffSample 2 =>
        (scalarFrameRealization U nu sigma hnu hsigma
          (oldCutoffSkewCoefficient m U ω)).energyBilin (r ω) (r ω) :=
      (hB.clm_apply hr).clm_apply hr
    convert hm using 1
    funext ω
    rw [hk ω]
    have := (scalar_field_energy_eq_bilin U nu sigma hnu hsigma
      (oldCutoffSkewCoefficient m U ω)
      (Lp.memLp (oldSignedCellResidual Q U hU nu sigma hnu hsigma
        (oldCutoffSkewCoefficient m Q ω) F hF)))
    rw [hres ω] at this
    rw [← this]
    exact (scalarFieldEnergy_eq_pairing U nu sigma hnu hsigma _ _).symm
  · have hm : Measurable fun ω : Cutoff.CutoffSample 2 =>
        pairingCLM (openCubeSet U) hw (r ω) :=
      (pairingCLM (openCubeSet U) hw).continuous.measurable.comp hr
    convert hm using 1
    funext ω
    have := pairingCLM_eq hw
      (Lp.memLp (oldSignedCellResidual Q U hU nu sigma hnu hsigma
        (oldCutoffSkewCoefficient m Q ω) F hF))
    rw [hres ω] at this
    exact this.symm

/-- The actual gap `Gap(ω) = Σ_i ‖Z*_i − Z_lift,i‖²_A` of the smooth-feedback
estimate is a measurable function of the OLD sample. -/
theorem smooth_feedback_h2_gap_measurable
    {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (u : ι → H10Function (openCubeSet Q))
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu
      (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
      (fun x => (u i).toH1Function.grad x) (Z ω i)) :
    Measurable fun ω : Cutoff.CutoffSample 2 =>
      ∑ i ∈ S, scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω)
        (Z ω i - oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
          (fun x => ((u i).toH1Function.grad x, 0))
          (memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero)) := by
  classical
  apply Finset.measurable_sum
  intro i _
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let f : Vec 2 → Vec 2 := fun x => (u i).toH1Function.grad x
  let hf : MemVectorL2 (openCubeSet Q) f := (u i).toH1Function.grad_memVectorL2
  let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
  let hF : MemBlockL2 (openCubeSet Q) F := memBlockL2_blockField hf MemLp.zero
  have hW : ScalarVariation (openCubeSet Q) F := by
    refine ⟨hF, ?_, ?_⟩
    · simpa [F, f] using (u i).isPotentialZeroTraceOn
    · exact isSolenoidalZeroNormalTraceOn_zero
  have hgap (ω : Cutoff.CutoffSample 2) :
      scalarFieldEnergy M.nu σ (oldCutoffSkewCoefficient m Q ω)
        (Z ω i - oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
          (oldCutoffSkewCoefficient m Q ω) F hF) =
      scalarFieldEnergy M.nu σ (oldCutoffSkewCoefficient m Q ω)
          (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF) -
        2 * scalarSourcePairing (openCubeSet Q) f
          (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF) +
        scalarFieldEnergy M.nu σ (oldCutoffSkewCoefficient m Q ω) (Z ω i) := by
    simpa [F, hF] using smooth_feedback_actual_local_lift_gap_identity Q depth
      M.nu σ M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω) f hW (Z ω i) (hZ ω i)
  have hN := smooth_feedback_maximizer_energy_measurable M m Q f hf
    (fun ω => Z ω i) (fun ω => hZ ω i)
  have hcells (U : OldSignedCellIndex Q depth) :
      Measurable (fun ω : Cutoff.CutoffSample 2 =>
        oldSignedEnergyPairing U.val M.nu σ
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            (oldCutoffSkewCoefficient m Q ω))
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF)
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF)) ∧
      Measurable (fun ω : Cutoff.CutoffSample 2 =>
        scalarSourcePairing (openCubeSet U.val) f
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF)) :=
    cell_residual_functionals_measurable m Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ F hF f
      (hf.mono_measure (Measure.restrict_mono_set volume
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)))
  have hE : Measurable fun ω : Cutoff.CutoffSample 2 =>
      scalarFieldEnergy M.nu σ (oldCutoffSkewCoefficient m Q ω)
        (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
          (oldCutoffSkewCoefficient m Q ω) F hF) := by
    have heq : (fun ω : Cutoff.CutoffSample 2 => scalarFieldEnergy M.nu σ
        (oldCutoffSkewCoefficient m Q ω)
        (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
          (oldCutoffSkewCoefficient m Q ω) F hF)) = fun ω =>
        oldSignedCellAverage Q depth (fun U =>
          oldSignedEnergyPairing U.val M.nu σ
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              (oldCutoffSkewCoefficient m Q ω))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ
              (oldCutoffSkewCoefficient m Q ω) F hF)
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ
              (oldCutoffSkewCoefficient m Q ω) F hF)) := by
      funext ω
      rw [scalarFieldEnergy_eq_pairing Q M.nu σ M.nu_pos hσ]
      exact old_signed_local_residual_cell_pairing Q depth M.nu σ M.nu_pos hσ
        (oldCutoffSkewCoefficient m Q ω) F F hF hF
    rw [heq]
    unfold oldSignedCellAverage
    exact (Finset.measurable_sum _ fun U _ => (hcells U).1).const_mul _
  have hP : Measurable fun ω : Cutoff.CutoffSample 2 =>
      scalarSourcePairing (openCubeSet Q) f
        (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
          (oldCutoffSkewCoefficient m Q ω) F hF) := by
    have heq : (fun ω : Cutoff.CutoffSample 2 => scalarSourcePairing (openCubeSet Q) f
        (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
          (oldCutoffSkewCoefficient m Q ω) F hF)) = fun ω =>
        oldSignedCellAverage Q depth (fun U =>
          scalarSourcePairing (openCubeSet U.val) f
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) M.nu σ M.nu_pos hσ
              (oldCutoffSkewCoefficient m Q ω) F hF)) := by
      funext ω
      exact smooth_feedback_source_local_residual_pairing_partition Q depth
        M.nu σ M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω) f hf
    rw [heq]
    unfold oldSignedCellAverage
    exact (Finset.measurable_sum _ fun U _ => (hcells U).2).const_mul _
  have hfun : (fun ω : Cutoff.CutoffSample 2 => scalarFieldEnergy M.nu σ
      (oldCutoffSkewCoefficient m Q ω)
      (Z ω i - oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
        (oldCutoffSkewCoefficient m Q ω) F hF)) = fun ω =>
      scalarFieldEnergy M.nu σ (oldCutoffSkewCoefficient m Q ω)
          (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF) -
        2 * scalarSourcePairing (openCubeSet Q) f
          (oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
            (oldCutoffSkewCoefficient m Q ω) F hF) +
        scalarFieldEnergy M.nu σ (oldCutoffSkewCoefficient m Q ω) (Z ω i) := by
    funext ω
    exact hgap ω
  change Measurable fun ω : Cutoff.CutoffSample 2 => scalarFieldEnergy M.nu σ
      (oldCutoffSkewCoefficient m Q ω)
      (Z ω i - oldSignedLocalResidual Q depth M.nu σ M.nu_pos hσ
        (oldCutoffSkewCoefficient m Q ω) F hF)
  rw [hfun]
  exact (hE.sub (hP.const_mul 2)).add hN

end

end ASDExplicitGamma.Scalar
