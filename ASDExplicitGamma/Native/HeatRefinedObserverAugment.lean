module

public import ASDExplicitGamma.Native.HeatRemainderControlAugmentNorm
public import ASDExplicitGamma.Native.HeatRefinedObserverShear

/-! Heat augmentation at the refined observer in the unchanged parent frame. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Gaussian Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- On cutoff law times auxiliary Gaussian law, the actual finite-band
sheared trace has the sharp square-root Lp envelope. Its physical trace norm
is retained for substitution of the individual/full-response producer profile;
the inverse norm is discharged internally from the original OLD rare bank.
The auxiliary shear is arbitrary measurable data, so this applies to each
coordinate of the actual correlated auxiliary vector without decoupling it. -/
theorem heat_refined_observer_augmented_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (q n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (hq : originCube 2 q ∈ descendantsAtDepth (originCube 2 n) r) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1)
    (g : (ℕ → ℝ) → ℝ) (hgmeas : Measurable g)
    (p : ℝ) (hp : 1 ≤ p) (hp128 : p ≤ 128) :
    eLpNorm (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      modelTraceObservable q M.nu (Annealed.sigmaBar M n)
        (heatRefinedObserverShear q n height t z.1 (g z.2)))
        (ENNReal.ofReal p) (nativeHeatRemainderJointLaw M) ≤
      (eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
          modelTraceObservable q M.nu (Annealed.sigmaBar M n) (parentBoundaryObserverBandScalar q n height t ω))
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ^ (1/2 : ℝ) +
        ENNReal.ofReal (2 * ((3683/2500 : ℝ) + 3/10^46)) ^ (1/2 : ℝ) *
          eLpNorm (fun ξ => g ξ / (Annealed.sigmaBar M n : ℝ)) (ENNReal.ofReal (2*p))
            standardGaussianInfinitePi)^2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let η := standardGaussianInfinitePi
  let R := nativeSourceBandRemainder M n height t
  let f := fun ω : Cutoff.CutoffSample 2 => modelTraceObservable q M.nu (Annealed.sigmaBar M n)
    (parentBoundaryObserverBandScalar q n height t ω)
  let d := fun ω : Cutoff.CutoffSample 2 => 2 * ((3683/2500 : ℝ) + R ω)
  let G := fun ξ : ℕ → ℝ => g ξ / (Annealed.sigmaBar M n : ℝ)
  let S := fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
    modelTraceObservable q M.nu (Annealed.sigmaBar M n)
      (heatRefinedObserverShear q n height t z.1 (g z.2))
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hp
  have hb := native_source_band_history_rare_split M h hM hg n height hpast t ht
  have hRm : Measurable R := hb.2.1
  have hR0 : ∀ ω, 0 ≤ R ω := hb.2.2.1
  have hfm : Measurable f :=
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
      (parent_boundary_observer_band_scalar_measurable q n height t)
  have hdm : Measurable d := (measurable_const.add hRm).const_mul 2
  have hGm : Measurable G := hgmeas.div_const _
  have hconst : Continuous (fun c : ℝ => ContinuousMap.const (closure (cubeSet (originCube 2 q))) c) := by
    exact (ContinuousLinearMap.const (R := ℝ) (closure (cubeSet (originCube 2 q))) : ℝ →L[ℝ] C(_, ℝ)).continuous
  have hscalar : Measurable (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      heatRefinedObserverShear q n height t z.1 (g z.2)) :=
    ((parent_boundary_observer_band_scalar_measurable q n height t).comp measurable_fst).add
      (hconst.measurable.comp (hgmeas.comp measurable_snd))
  have hSm : Measurable S :=
    (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp hscalar
  have hf0 (ω : Cutoff.CutoffSample 2) : 0 ≤ f ω :=
    modelTraceObservable_nonneg q M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 _
  have hd0 (ω : Cutoff.CutoffSample 2) : 0 ≤ d ω := by dsimp [d]; positivity [hR0 ω]
  have hS0 (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : 0 ≤ S z :=
    modelTraceObservable_nonneg q M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 _
  have hpoint : ∀ᵐ z ∂μ.prod η, S z ≤ (Real.sqrt (f z.1) + Real.sqrt (d z.1) * |G z.2|)^2 := by
    have hh : ∀ᵐ z ∂μ.prod η,∀ c : ℝ,
        modelTraceObservable q M.nu (Annealed.sigmaBar M n)
          (heatRefinedObserverShear q n height t z.1 c) ≤
        (Real.sqrt (f z.1)+|c/(Annealed.sigmaBar M n:ℝ)| *Real.sqrt (d z.1))^2 :=
      measurePreserving_fst.quasiMeasurePreserving.ae
        (heat_refined_observer_shear_trace_ae_le M h hM hg q n r hr hq height hpast t ht)
    filter_upwards [hh] with z hz
    simpa only [f,d,R,G,S,mul_comm] using hz (g z.2)
  have hRnorm : eLpNorm R (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (3/10^46 : ℝ) := by
    have hle : ENNReal.ofReal p ≤ (128 : ℝ≥0∞) := by
      exact_mod_cast (ENNReal.ofReal_le_ofReal hp128)
    have hm := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := R) (μ := μ) hle hRm.aestronglyMeasurable
    simp only [measure_univ, ENNReal.one_rpow, mul_one] at hm
    exact hm.trans hb.2.2.2.1
  have hconstant : eLpNorm (fun _ : Cutoff.CutoffSample 2 => (3683/2500 : ℝ))
      (ENNReal.ofReal p) μ = ENNReal.ofReal (3683/2500 : ℝ) := by
    rw [eLpNorm_const' _ (by positivity) ENNReal.ofReal_ne_top]
    simp [Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 3683/2500)]
  have hadd := eLpNorm_add_le (f := fun _ : Cutoff.CutoffSample 2 => (3683/2500 : ℝ))
    (g := R) (μ := μ) (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by exact_mod_cast ENNReal.ofReal_le_ofReal hp)
  rw [hconstant] at hadd
  have hplus : eLpNorm (fun ω => (3683/2500 : ℝ) + R ω) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((3683/2500 : ℝ) + 3/10^46) := by
    have hh := hadd.trans (add_le_add le_rfl hRnorm)
    simpa only [Pi.add_def, ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 3683/2500) (by positivity : (0 : ℝ) ≤ 3/10^46)] using hh
  have hdnorm : eLpNorm d (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2*((3683/2500 : ℝ)+3/10^46)) := by
    have he : d = (2 : ℝ) • (fun ω => (3683/2500 : ℝ) + R ω) := by funext ω; rfl
    rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    exact (mul_le_mul' (le_refl (ENNReal.ofReal 2)) hplus).trans_eq
      (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hbound := nativeHeat_shear_envelope_Lp μ η f d G S hfm.aestronglyMeasurable hdm.aestronglyMeasurable
    hGm.aestronglyMeasurable hSm.aestronglyMeasurable hf0 hd0 hS0 hpoint p hp
  apply hbound.trans
  apply pow_le_pow_left'
  exact add_le_add le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hdnorm (by norm_num : (0 : ℝ) ≤ 1/2)) le_rfl)

end
end ASDExplicitGamma.Native
