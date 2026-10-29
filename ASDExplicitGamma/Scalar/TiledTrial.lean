module

public import ASDExplicitGamma.Scalar.TrialIntegrability
public import ASDExplicitGamma.Scalar.CutoffTiling

/-! Exact complete expected energy of the source trial tiled over a finite parent. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- The source compatible field with all same-scale translated cell corrections inserted. -/
def tiledBandTrial (M : ABKModel 2) (n N : ℤ) (σ : ℝ) (e : Vec 2)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2) (Q : TriadicCube 2) (q : ℤ)
    (ω : CutoffSample 2) : Vec 2 → BlockVec 2 :=
  compatibleCellPatch (bandLoad M n N σ e ω) (descendantsAtScale Q q) openCubeSet
    (fun R => bandTrialField M n N σ e (translatedCellCorrection C R) ω)

theorem ae_translated_correction (M : ABKModel 2) (q : ℤ)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hC : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet (originCube 2 q)) (C ω))
    (R : TriadicCube 2) (hR : R.scale=q) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet R) (translatedCellCorrection C R ω) := by
  let z := triadicCubeShift R
  have hmp : MeasurePreserving (fun ω : CutoffSample 2 => z +ᵥ ω)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_translateCutoffSample z, Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩
  filter_upwards [hmp.quasiMeasurePreserving.ae hC] with ω hω
  have htrans := scalarVariation_translateSet hω z
  have hset : openCubeSet R = translateSet z (openCubeSet (originCube 2 q)) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, hR]
  rw [← hset] at htrans
  exact htrans

theorem integrable_translated_trial_energy (M : ABKModel 2) (n N q : ℤ)
    (σ : ℝ) (e : Vec 2) (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hE : Integrable (cutoffTrialEnergy M N σ (originCube 2 q)
      (bandTrialField M n N σ e C)) (Cutoff.cutoffSampleLaw M).toMeasure)
    (R : TriadicCube 2) (hR : R.scale=q) :
    Integrable (cutoffTrialEnergy M N σ R
      (bandTrialField M n N σ e (translatedCellCorrection C R)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmp : MeasurePreserving (fun ω : CutoffSample 2 => triadicCubeShift R +ᵥ ω)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    ⟨Cutoff.measurable_translateCutoffSample _, Cutoff.map_translateCutoffSample_cutoffSampleLaw M _⟩
  exact (hmp.integrable_comp_of_integrable hE).congr (Filter.Eventually.of_forall fun ω =>
    (translated_trial_energy M n N q σ e C R hR ω).symm)

/-- The tiled trial's complete expected normalized energy is exactly the
source single-cell energy, at every larger finite parent. -/
theorem integral_tiled_trial_energy (M : ABKModel 2) (n N q : ℤ) (σ : ℝ)
    (hσ : 0 < σ) (e : Vec 2) (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hC : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet (originCube 2 q)) (C ω))
    (hE : Integrable (cutoffTrialEnergy M N σ (originCube 2 q)
      (bandTrialField M n N σ e C)) (Cutoff.cutoffSampleLaw M).toMeasure)
    (Q : TriadicCube 2) (hq : q ≤ Q.scale) :
    Integrable (cutoffTrialEnergy M N σ Q (tiledBandTrial M n N σ e C Q q))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, cutoffTrialEnergy M N σ Q (tiledBandTrial M n N σ e C Q q) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, cutoffTrialEnergy M N σ (originCube 2 q) (bandTrialField M n N σ e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let s := descendantsAtScale Q q
  let A := fun R => bandTrialField M n N σ e (translatedCellCorrection C R)
  let E := fun R => cutoffTrialEnergy M N σ R (A R)
  have hmem (R : TriadicCube 2) (hR : R ∈ s) :
      ∀ᵐ ω ∂μ, MemBlockL2 (openCubeSet R) (A R ω) := by
    have hscale := scale_eq_of_mem_descendantsAtScale hR
    filter_upwards [ae_memBlockL2_bandLoad M n N σ e R,
      ae_translated_correction M q C hC R hscale] with ω hload hcorr
    exact hload.add hcorr.1
  have hall : ∀ᵐ ω ∂μ, ∀ R, R ∈ s → MemBlockL2 (openCubeSet R) (A R ω) := by
    rw [ae_all_iff]
    intro R
    by_cases hR : R ∈ s
    · exact (hmem R hR).mono fun ω hω _ => hω
    · exact Filter.Eventually.of_forall fun ω h => (hR h).elim
  have heq : (cutoffTrialEnergy M N σ Q (tiledBandTrial M n N σ e C Q q)) =ᵐ[μ]
      fun ω => ∑ R ∈ s, (cubeVolume R/cubeVolume Q)*E R ω := by
    filter_upwards [hall] with ω hω
    exact tiled_patch_energy Q q hq (bandLoad M n N σ e ω) (fun R => A R ω)
      (fun x F => Response.responseFrameEnergyDensity M.nu σ (Cutoff.cutoff N ω x 1 0) F)
      (fun R hR => cutoff_energy_density_integrableOn M N σ hσ R ω (A R ω) (hω R hR))
  have hInt (R : TriadicCube 2) (hR : R ∈ s) : Integrable (E R) μ :=
    integrable_translated_trial_energy M n N q σ e C hE R
      (scale_eq_of_mem_descendantsAtScale hR)
  have hsum := integrable_finsetSum s (fun R hR => (hInt R hR).const_mul (cubeVolume R/cubeVolume Q))
  refine ⟨hsum.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_finsetSum _ (fun R hR => (hInt R hR).const_mul _)]
  simp_rw [integral_const_mul]
  have hmean (R : TriadicCube 2) (hR : R ∈ s) : (∫ ω, E R ω ∂μ) =
      ∫ ω, cutoffTrialEnergy M N σ (originCube 2 q) (bandTrialField M n N σ e C) ω ∂μ :=
    integral_translated_trial_energy M n N q σ e C R (scale_eq_of_mem_descendantsAtScale hR)
  rw [Finset.sum_congr rfl (fun R hR => congrArg (fun t => (cubeVolume R/cubeVolume Q)*t) (hmean R hR))]
  rw [← Finset.sum_mul, descendant_cell_weights_sum Q q hq, one_mul]

/-- The complete trial inserts precisely the translated source corrections. -/
theorem tiled_trial_eq_background_add_corrections (M : ABKModel 2) (n N : ℤ)
    (σ : ℝ) (e : Vec 2) (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (Q : TriadicCube 2) (q : ℤ) (ω : CutoffSample 2) :
    tiledBandTrial M n N σ e C Q q ω = bandLoad M n N σ e ω +
      ∑ R ∈ descendantsAtScale Q q, (openCubeSet R).indicator (translatedCellCorrection C R ω) := by
  have hc (R : TriadicCube 2) : bandTrialField M n N σ e (translatedCellCorrection C R) ω -
      bandLoad M n N σ e ω = translatedCellCorrection C R ω := by
    unfold bandTrialField
    abel
  unfold tiledBandTrial compatibleCellPatch
  simp_rw [hc]
  funext x
  simp only [Pi.add_apply, Finset.sum_apply]

theorem descendant_correction_sum_variation (Q : TriadicCube 2) (q : ℤ)
    (hq : q ≤ Q.scale) (C : TriadicCube 2 → Vec 2 → BlockVec 2)
    (hC : ∀ R ∈ descendantsAtScale Q q, ScalarVariation (openCubeSet R) (C R)) :
    ScalarVariation (openCubeSet Q)
      (∑ R ∈ descendantsAtScale Q q, (openCubeSet R).indicator (C R)) := by
  apply scalar_variation_finset_sum
  intro R hR
  have hsub : openCubeSet R ⊆ openCubeSet Q := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hq] at hR
    exact openCubeSet_subset_of_mem_descendantsAtDepth hR
  exact scalar_variation_zero_extension (isOpen_openCubeSet R) (isOpen_openCubeSet Q)
    hsub (hC R hR)

theorem tiled_trial_memBlockL2 (M : ABKModel 2) (n N : ℤ) (σ : ℝ) (e : Vec 2)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2) (Q : TriadicCube 2) (q : ℤ)
    (hq : q ≤ Q.scale) (ω : CutoffSample 2)
    (hload : MemBlockL2 (openCubeSet Q) (bandLoad M n N σ e ω))
    (hC : ∀ R ∈ descendantsAtScale Q q,
      ScalarVariation (openCubeSet R) (translatedCellCorrection C R ω)) :
    MemBlockL2 (openCubeSet Q) (tiledBandTrial M n N σ e C Q q ω) := by
  rw [tiled_trial_eq_background_add_corrections]
  exact hload.add (descendant_correction_sum_variation Q q hq _ hC).1

/-- Replacing the stationary background flux by its zero-normal cutoff
produces a genuine parent competitor with all source corrections retained. -/
theorem tiled_trial_bottom_error_admissible (M : ABKModel 2) (n N : ℤ)
    (σ : ℝ) (e : Vec 2) (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (Q : TriadicCube 2) (q : ℤ) (hq : q ≤ Q.scale) (ω : CutoffSample 2)
    (w : Vec 2 → Vec 2) (hw : ScalarVariation (openCubeSet Q) (scalarBottomLoad w))
    (hC : ∀ R ∈ descendantsAtScale Q q,
      ScalarVariation (openCubeSet R) (translatedCellCorrection C R ω)) :
    ScalarVariation (openCubeSet Q)
      (tiledBandTrial M n N σ e C Q q ω +
        (fun x => ((0:Vec 2), w x-(realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec)) -
          constantBlockLoad (e,0)) := by
  let D := fun x => ((0:Vec 2), w x-(realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec)
  have hbase : bandLoad M n N σ e ω + D - constantBlockLoad (e,0) =
      scalarBottomLoad w := by
    funext x
    apply Prod.ext
    · funext i
      change e i + 0 - e i = 0
      ring
    · funext i
      change (realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec i +
        (w x i-(realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec i)-0 = w x i
      ring
  rw [tiled_trial_eq_background_add_corrections]
  change ScalarVariation (openCubeSet Q) ((_+_)+D-constantBlockLoad (e,0))
  have hreorder : (bandLoad M n N σ e ω +
      ∑ R ∈ descendantsAtScale Q q, (openCubeSet R).indicator (translatedCellCorrection C R ω)) +
      D-constantBlockLoad (e,0) =
      scalarBottomLoad w +
        ∑ R ∈ descendantsAtScale Q q, (openCubeSet R).indicator (translatedCellCorrection C R ω) := by
    rw [← hbase]
    abel
  rw [hreorder]
  exact scalar_variation_add hw (descendant_correction_sum_variation Q q hq _ hC)

end
end ASDExplicitGamma.Scalar
