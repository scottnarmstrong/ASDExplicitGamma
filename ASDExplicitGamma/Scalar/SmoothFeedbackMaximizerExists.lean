/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackMaximizerMeasurable
public import ASDExplicitGamma.Native.OldSignedCellProjection

/-! Existence and uniqueness of the OLD-law maximizer `Z*` in `V_Q`, and its
canonical definition. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- Lax–Milgram representer of a bounded functional for a coercive form. -/
theorem exists_form_rep {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : IsCoercive B) (ℓ : E →L[ℝ] ℝ) :
    ∃ Y : E, ∀ T : E, B Y T = ℓ T := by
  let e := hB.continuousLinearEquivOfBilin
  refine ⟨e.symm ((InnerProductSpace.toDual ℝ E).symm ℓ), fun T => ?_⟩
  rw [← hB.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply]
  simp [InnerProductSpace.toDual_symm_apply]

/-- The actual OLD maximizer: the energy projection onto `V_Q` of the Lax–Milgram
representer of the source functional. -/
def oldMaximizer (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w) (ω : Cutoff.CutoffSample 2) : Vec 2 → BlockVec 2 :=
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  let hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  let R := scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (oldCutoffSkewCoefficient m Q ω)
  let Y := Classical.choose (exists_form_rep R.energyBilin R.energyCoercive
    (pairingCLM (openCubeSet Q) hw))
  hilbertBlockL2ToBlockL2 (Y - scalarProjectionResidual Q M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω) Y)

theorem oldMaximizer_spec (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w) (ω : Cutoff.CutoffSample 2) :
    IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) w
      (oldMaximizer M m Q w hw ω) := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  let k := oldCutoffSkewCoefficient m Q ω
  let R := scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k
  let ℓ := pairingCLM (openCubeSet Q) hw
  have hY := Classical.choose_spec (exists_form_rep R.energyBilin R.energyCoercive ℓ)
  set Y := Classical.choose (exists_form_rep R.energyBilin R.energyCoercive ℓ) with hYdef
  set z := Y - scalarProjectionResidual Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k Y
    with hz
  have hzK : z ∈ R.correctionSpace.correctionSpace :=
    scalar_projection_removed_mem Q M.nu _ M.nu_pos hσ k Y
  have hzvar : ScalarVariation (openCubeSet Q) (hilbertBlockL2ToBlockL2 z) :=
    old_signed_hilbert_correction_variation Q M.nu _ M.nu_pos hσ k z hzK
  have hrebuild : toHilbertBlockL2OfBlockField hzvar.1 = z := by
    have := hilbert_field_rebuild z
    simpa using this
  have heuler : ∀ T ∈ R.correctionSpace.correctionSpace, R.energyBilin z T = ℓ T := by
    intro T hT
    have h0 := scalar_projection_residual_orthogonal Q M.nu _ M.nu_pos hσ k Y T hT
    rw [hz, map_sub, ContinuousLinearMap.sub_apply, h0, sub_zero, hY]
  have hMdef : oldMaximizer M m Q w hw ω = hilbertBlockL2ToBlockL2 z := rfl
  rw [hMdef]
  refine ⟨hzvar, fun T hT => ?_⟩
  have htK := scalar_variation_mem_frame_correction Q M.nu _ M.nu_pos hσ k hT
  have e1 := heuler _ htK
  have e2 := heuler _ hzK
  have hsym := R.energySymm z (toHilbertBlockL2OfBlockField hT.1)
  have hcoer := R.energyCoercive
  obtain ⟨C, hC, hCle⟩ := hcoer
  have hnn := hCle (z - toHilbertBlockL2OfBlockField hT.1)
  have hexp : R.energyBilin (z - toHilbertBlockL2OfBlockField hT.1)
      (z - toHilbertBlockL2OfBlockField hT.1) =
      R.energyBilin z z - R.energyBilin z (toHilbertBlockL2OfBlockField hT.1) -
        R.energyBilin (toHilbertBlockL2OfBlockField hT.1) z +
        R.energyBilin (toHilbertBlockL2OfBlockField hT.1) (toHilbertBlockL2OfBlockField hT.1) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    ring
  have hpos : 0 ≤ C * ‖z - toHilbertBlockL2OfBlockField hT.1‖ *
      ‖z - toHilbertBlockL2OfBlockField hT.1‖ := by positivity
  have hs1 : ℓ (toHilbertBlockL2OfBlockField hT.1) =
      scalarSourcePairing (openCubeSet Q) w _ := pairingCLM_eq hw hT.1
  have hs2 : ℓ (toHilbertBlockL2OfBlockField hzvar.1) =
      scalarSourcePairing (openCubeSet Q) w _ := pairingCLM_eq hw hzvar.1
  have hb1 := scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ k hT.1
  have hb2 := scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ k hzvar.1
  rw [hrebuild] at hs2 hb2
  rw [← hs1, ← hs2, hb1, hb2]
  linarith

theorem oldMaximizer_unique (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (w : Vec 2 → Vec 2) (hw : MemVectorL2 (openCubeSet Q) w) (ω : Cutoff.CutoffSample 2)
    {Z₁ Z₂ : Vec 2 → BlockVec 2}
    (h₁ : IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) w Z₁)
    (h₂ : IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) w Z₂) :
    Z₁ =ᵐ[volumeMeasureOn (openCubeSet Q)] Z₂ := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  let k := oldCutoffSkewCoefficient m Q ω
  have hd : ScalarVariation (openCubeSet Q) (Z₁ - Z₂) := by
    have := scalar_variation_add h₁.1 (scalar_variation_smul h₂.1 (-1))
    simpa [sub_eq_add_neg] using this
  have e1 := smooth_feedback_maximizer_variation_euler Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k w hw Z₁ _ h₁ hd
  have e2 := smooth_feedback_maximizer_variation_euler Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k w hw Z₂ _ h₂ hd
  have hsub := old_signed_energy_pairing_sub_left Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k h₁.1.1 h₂.1.1 hd.1
  have hzero : oldSignedEnergyPairing Q M.nu (Annealed.sigmaBar M m : ℝ) k (Z₁ - Z₂) (Z₁ - Z₂) = 0 := by
    rw [hsub, ← e1, ← e2]; ring
  have hsF : scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ) k (Z₁ - Z₂) = 0 := by
    rw [scalarFieldEnergy_eq_pairing Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k]; exact hzero
  rw [scalar_field_energy_eq_bilin Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k hd.1] at hsF
  obtain ⟨C, hC, hCle⟩ := (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ k).energyCoercive
  have := hCle (toHilbertBlockL2OfBlockField hd.1)
  rw [hsF] at this
  have hn : ‖toHilbertBlockL2OfBlockField hd.1‖ = 0 := by
    by_contra hne
    have : 0 < C * ‖toHilbertBlockL2OfBlockField hd.1‖ * ‖toHilbertBlockL2OfBlockField hd.1‖ := by
      have := norm_pos_iff.mpr (norm_ne_zero_iff.mp hne)
      positivity
    linarith
  have h0 : toHilbertBlockL2OfBlockField hd.1 = 0 := norm_eq_zero.mp hn
  have hae := coeFn_toHilbertBlockL2OfBlockField hd.1
  rw [h0] at hae
  filter_upwards [hae, Lp.coeFn_zero (E := HilbertBlockVec 2) (p := 2)
    (μ := volumeMeasureOn (openCubeSet Q))] with x hx hx0
  have h1 : hilbertifyBlockField (Z₁ - Z₂) x = 0 := by
    rw [← hx]; simpa using hx0
  have h3 := congrArg HilbertBlockVec.toBlockVec h1
  simp only [hilbertifyBlockField, HilbertBlockVec.toBlockVec_ofBlockVec] at h3
  have h4 : (Z₁ - Z₂) x = 0 := by
    rw [h3]; ext <;> simp [HilbertBlockVec.toBlockVec]
  exact sub_eq_zero.mp h4

end

end ASDExplicitGamma.Scalar
