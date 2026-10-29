module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetGaussianDerivative
public import ASDExplicitGamma.Gaussian.DerivativeLawObservationCovariance
public import ASDExplicitGamma.Model.CutoffAction

/-! Strong derivatives of the literal finite band, consuming exactly the
joint stored-jet Gaussian conclusion supplied by the BandGaussian. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Frozen.Assumptions ASDExplicitGamma.Gaussian
noncomputable section

/-- Literal finite-band observations, definitionally the band-jet carrier. -/
def upperCellResetBandJet {b : ℕ} (k : Fin b → ℤ) (w : Fin b → ℝ)
    (o : ShellDerivativeObservation) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i,w i*shellDerivativeEval o (ω.val (k i))

theorem upper_cell_reset_band_jet_memLp {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (w : Fin b → ℝ)
    (hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w)) (o : ShellDerivativeObservation) :
    MemLp (upperCellResetBandJet k w o) 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
  obtain ⟨v,hv⟩ := hGaussian.map_single o
  exact memLp_of_map_gaussianReal (hGaussian.1 o) hv 2 (by norm_num)

/-- Actual L2 class of a stored finite-band observation. -/
def upperCellResetBandJetClass {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (w : Fin b → ℝ)
    (hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w)) (o : ShellDerivativeObservation) :
    Algsuperdiff.Probability.Stationary.ScalarL2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  (upper_cell_reset_band_jet_memLp M k w hGaussian o).toLp (upperCellResetBandJet k w o)

/-- The complete actual band has its stored first derivative as a strong L2
derivative. The sole producer premise is the exact joint Gaussian jet law;
no moment estimate, domination, or corrected-field regularity is a premise. -/
theorem upper_cell_reset_band_strong_derivative {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (w : Fin b → ℝ)
    (hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w)) (x v : Vec 2) :
    HasDerivAt (fun t : ℝ => upperCellResetBandJetClass M k w hGaussian (.value (x+t • v)))
      (upperCellResetBandJetClass M k w hGaussian (.first x v)) 0 := by
  apply upper_cell_reset_gaussian_hasDerivAt_L2 (Cutoff.cutoffSampleLaw M).toMeasure
    _ _ (fun t => upperCellResetBandJet k w (.value (x+t • v)))
    (upperCellResetBandJet k w (.first x v))
  · intro t
    exact (upper_cell_reset_band_jet_memLp M k w hGaussian _).coeFn_toLp
  · exact (upper_cell_reset_band_jet_memLp M k w hGaussian _).coeFn_toLp
  · exact hGaussian.sum_reindex (fun t : ℝ => .value (x+t • v)) (fun _ : Unit => .first x v)
  · apply Filter.Eventually.of_forall
    intro ω
    have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin b))) =>
      (shellScalarValue_line_hasDerivAt (ω.val (k i)) x v 0).const_mul (w i))
    simpa only [upperCellResetBandJet,shellDerivativeEval,shellScalarFirst,
      zero_smul,add_zero] using hh

/-- Translating the scalar class translates only the marginal physical band
observation; the cutoff law and all shell indices stay unchanged. -/
theorem upper_cell_reset_band_class_translate {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (w : Fin b → ℝ)
    (hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w)) (x z : Vec 2) :
    koopman z (upperCellResetBandJetClass M k w hGaussian (.value x))=
      upperCellResetBandJetClass M k w hGaussian (.value (x+z)) := by
  apply Lp.ext
  have hrep : (upperCellResetBandJetClass M k w hGaussian (.value x) :
      Cutoff.CutoffSample 2 → ℝ) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      upperCellResetBandJet k w (.value x) :=
    (upper_cell_reset_band_jet_memLp M k w hGaussian (.value x)).coeFn_toLp
  have hpull := (measurePreserving_const_vadd (μ := (Cutoff.cutoffSampleLaw M).toMeasure) z).quasiMeasurePreserving.ae hrep
  have hfinal : (upperCellResetBandJetClass M k w hGaussian (.value (x+z)) :
      Cutoff.CutoffSample 2 → ℝ) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      upperCellResetBandJet k w (.value (x+z)) :=
    (upper_cell_reset_band_jet_memLp M k w hGaussian (.value (x+z))).coeFn_toLp
  filter_upwards [coeFn_koopman z (upperCellResetBandJetClass M k w hGaussian (.value x)),
    hpull,hfinal]
    with ω ht hx hz
  rw [ht,hx,hz]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- The actual scalar-band Koopman orbit has the literal stored derivative.
This is the forcing input consumed by full-flux derivative transport. -/
theorem upper_cell_reset_band_horizontal_derivative {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (w : Fin b → ℝ)
    (hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w)) (v : Vec 2) :
    HasDerivAt (fun t : ℝ => koopman (t • v)
      (upperCellResetBandJetClass M k w hGaussian (.value 0)))
      (upperCellResetBandJetClass M k w hGaussian (.first 0 v)) 0 := by
  simpa only [upper_cell_reset_band_class_translate,zero_add] using
    upper_cell_reset_band_strong_derivative M k w hGaussian 0 v

/-- Replacing Gaussian observations by AE-equivalent representatives
preserves their full finite joint law, not merely their marginal laws. -/
theorem upper_cell_reset_gaussian_family_congr
    {Ω I : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X Y : I → Ω → ℝ} (hX : IsCenteredGaussianFamily μ X)
    (heq : ∀ i,X i =ᵐ[μ] Y i) : IsCenteredGaussianFamily μ Y := by
  refine ⟨fun i => (hX.1 i).congr (heq i),?_⟩
  intro J _ x t
  obtain ⟨v,hv⟩ := hX.2 x t
  refine ⟨v,?_⟩
  rw [←hv]
  apply Measure.map_congr
  have ha := ae_all_iff.mpr (fun j : J => heq (x j))
  filter_upwards [ha] with ω hω
  exact Finset.sum_congr rfl (fun j _ => congrArg (fun a : ℝ => t j*a) (hω j).symm)

/-- The actual scalar-band Koopman orbit is jointly Gaussian on the original
cutoff law, proved from the exact stored-jet producer and marginal translation.
This supplies the forcing-orbit input of the full Helmholtz Gaussian reduction. -/
theorem upper_cell_reset_band_orbit_gaussian {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (w : Fin b → ℝ)
    (hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w)) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (fun z : Vec 2 => fun ω => koopman z
        (upperCellResetBandJetClass M k w hGaussian (.value 0)) ω) := by
  apply upper_cell_reset_gaussian_family_congr (Cutoff.cutoffSampleLaw M).toMeasure
    (hGaussian.comp (fun z : Vec 2 => .value z))
  intro z
  have ht : koopman z (upperCellResetBandJetClass M k w hGaussian (.value 0))=
      upperCellResetBandJetClass M k w hGaussian (.value z) := by
    simpa only [zero_add] using upper_cell_reset_band_class_translate M k w hGaussian 0 z
  rw [ht]
  exact (upper_cell_reset_band_jet_memLp M k w hGaussian (.value z)).coeFn_toLp.symm

end
end ASDExplicitGamma.Scalar
