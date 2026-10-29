module

public import ASDExplicitGamma.Scalar.CellTranslation
public import ASDExplicitGamma.Scalar.CutoffStream
public import Homogenization.Geometry.TriadicCubeTranslation

/-! The actual compatible cell trial, its translated corrections and full energy. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- The source compatible band load X=(e,v), in its old true scalar frame. -/
def bandLoad (M : ABKModel 2) (n N : ℤ) (σ : ℝ) (e : Vec 2)
    (ω : CutoffSample 2) (x : Vec 2) : BlockVec 2 :=
  (e, (realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec)

/-- A cell trial is the prescribed compatible band load plus its actual
zero-boundary correction. This retains its full principal/residual energy. -/
def bandTrialField (M : ABKModel 2) (n N : ℤ) (σ : ℝ) (e : Vec 2)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2) (ω : CutoffSample 2) : Vec 2 → BlockVec 2 :=
  bandLoad M n N σ e ω + C ω

/-- Translate a single origin-cell correction to any cell of the same scale. -/
def translatedCellCorrection (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (R : TriadicCube 2) (ω : CutoffSample 2) (x : Vec 2) : BlockVec 2 :=
  C (triadicCubeShift R +ᵥ ω) (x-triadicCubeShift R)

/-- The complete doubled OLD-frame energy for the unchanged terminal coefficient. -/
def cutoffTrialEnergy (M : ABKModel 2) (N : ℤ) (σ : ℝ) (Q : TriadicCube 2)
    (F : CutoffSample 2 → Vec 2 → BlockVec 2) (ω : CutoffSample 2) : ℝ :=
  volumeAverage (openCubeSet Q) (fun x =>
    responseFrameEnergyDensity M.nu σ (Cutoff.cutoff N ω x 1 0) (F ω x))

theorem cutoff_shift_value (N : ℤ) (z x : Vec 2) (ω : CutoffSample 2) :
    Cutoff.cutoff N (z +ᵥ ω) x 1 0 = Cutoff.cutoff N ω (x+z) 1 0 := by
  change Cutoff.cutoff N (Cutoff.translateCutoffSample z ω) x 1 0 = _
  exact (congrArg (fun a : RegCoeffField 2 => a x 1 0)
    (Cutoff.cutoff_translateCutoffSample N z ω)).symm

theorem stronglyMeasurable_bandLoad (M : ABKModel 2) (n N : ℤ) (σ : ℝ) (e : Vec 2) :
    StronglyMeasurable (Function.uncurry (bandLoad M n N σ e)) := by
  have hflux := stronglyMeasurable_uncurry_realize (d := 2)
    (stronglyMeasurable_cutoffBandFlux M n N σ⁻¹ e)
  exact stronglyMeasurable_const.prodMk
    ((HilbertVec.continuousLinearEquivVec 2).continuous.comp_stronglyMeasurable hflux)

theorem cutoffTrialEnergy_nonneg (M : ABKModel 2) (N : ℤ) (σ : ℝ) (hσ : 0 < σ)
    (Q : TriadicCube 2) (F : CutoffSample 2 → Vec 2 → BlockVec 2) (ω : CutoffSample 2) :
    0 ≤ cutoffTrialEnergy M N σ Q F ω := by
  unfold cutoffTrialEnergy volumeAverage
  apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_nonneg
  intro x
  unfold responseFrameEnergyDensity
  exact add_nonneg (mul_nonneg (div_nonneg M.nu_pos.le hσ.le) (vecNormSq_nonneg _))
    (mul_nonneg (div_nonneg hσ.le M.nu_pos.le) (vecNormSq_nonneg _))

theorem translated_trial_field (M : ABKModel 2) (n N : ℤ) (σ : ℝ) (e : Vec 2)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2) (R : TriadicCube 2)
    (ω : CutoffSample 2) (x : Vec 2) :
    bandTrialField M n N σ e (translatedCellCorrection C R) ω (x+triadicCubeShift R) =
      bandTrialField M n N σ e C (triadicCubeShift R +ᵥ ω) x := by
  unfold bandTrialField bandLoad translatedCellCorrection
  simp only [Pi.add_apply, add_sub_cancel_right]
  rw [realize_cutoffBandFlux_shift_sample]

/-- The normalized complete source energy on every translated cell is the
same origin-cell observable evaluated at the translated sample. -/
theorem translated_trial_energy (M : ABKModel 2) (n N q : ℤ) (σ : ℝ) (e : Vec 2)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2) (R : TriadicCube 2) (hR : R.scale=q)
    (ω : CutoffSample 2) :
    cutoffTrialEnergy M N σ R
      (bandTrialField M n N σ e (translatedCellCorrection C R)) ω =
      cutoffTrialEnergy M N σ (originCube 2 q) (bandTrialField M n N σ e C)
        (triadicCubeShift R +ᵥ ω) := by
  have hset : openCubeSet R =
      translateSet (triadicCubeShift R) (openCubeSet (originCube 2 q)) := by
    rw [openCubeSet_eq_translateSet_originCube_of_triadicCube R, hR]
  unfold cutoffTrialEnergy volumeAverage
  rw [hset, volume_translateSet_eq, ← setIntegral_comp_addRight_translateSet]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [translated_trial_field, cutoff_shift_value]

/-- Stationarity alone, without independence of cells, identifies their
complete expected energies. -/
theorem integral_translated_trial_energy (M : ABKModel 2) (n N q : ℤ)
    (σ : ℝ) (e : Vec 2) (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (R : TriadicCube 2) (hR : R.scale=q) :
    (∫ ω, cutoffTrialEnergy M N σ R
      (bandTrialField M n N σ e (translatedCellCorrection C R)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∫ ω, cutoffTrialEnergy M N σ (originCube 2 q) (bandTrialField M n N σ e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  simp_rw [translated_trial_energy M n N q σ e C R hR]
  exact integral_cutoffSample_vadd M (triadicCubeShift R) _

end
end ASDExplicitGamma.Scalar
