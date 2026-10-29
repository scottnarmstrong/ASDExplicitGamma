module

public import ASDExplicitGamma.Native.HeatIndividualComparison
public import ASDExplicitGamma.Native.GenericSourceChildInitial
public import ASDExplicitGamma.Numerics.Native.Gap001Certificate
public import ASDExplicitGamma.Numerics.Native.HeatParametersData

/-! The lag -1 child L^20 cap from the gap-one individual system. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

private theorem nativeRefinedChild_result20_le :
    (nativeGap001Result.getD 20 0 : ℚ) ≤
      ((5 / 2 : ℚ) / ((3 / 50 : ℚ) * nativeGap001Scale)) ^ 20 := by
  decide +kernel

/-- The actual gap-one band observable has an old-frame L^20 cap `5/2`,
read off the configured individual system at time one. -/
theorem nativeRefinedChild_bandObservable_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (hstate : nativeInductionState M h n) :
    eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable n M.nu (Annealed.sigmaBar M n)
        (nativeSourceBandScalar n 1 1 ω)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5 / 2) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let Φ := modelTraceObservable n M.nu (Annealed.sigmaBar M n)
  let f : Cutoff.CutoffSample 2 → ℝ := fun ω => Φ (nativeSourceBandScalar n 1 1 ω)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1
  have hΦ0 := modelTraceObservable_nonneg n M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => hΦ0 _
  have hpower := hasPolynomiallyBoundedC2Derivatives_rpow hΦ hΦ0 (by norm_num : (2:ℝ) ≤ 20)
  have hmem := native_source_band_test_memLp M h hM n 1 le_rfl (fun x => Φ x ^ (20 : ℝ))
    hpower.1.continuous.measurable
    (by obtain ⟨C, hC, d, h1, _⟩ := hpower.2; exact ⟨C, hC, d, h1⟩) 1 2 (by norm_num)
  have hpow : Integrable (fun ω => f ω ^ (20 : ℝ)) μ :=
    hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2)
  have hcmp := native_individual_cooperative_comparison M h hM hg n hpast hstate 0 1
    ⟨zero_le_one, le_rfl⟩ ⟨20, by norm_num⟩
  have hz : (0 : ℝ) < ((3 / 50 : ℚ) : ℝ) * (nativeGap001Scale : ℝ) := by
    have := nativeGap001Scale_pos
    positivity
  have hmoment : ∫ ω, f ω ^ (20 : ℝ) ∂μ ≤ (5 / 2 : ℝ) ^ 20 := by
    have hu : nativeIndividualNormalizedMomentCurve M n 0 1 ⟨20, by norm_num⟩ =
        (∫ ω, f ω ^ (20 : ℝ) ∂μ) /
          ((3 / 50 : ℝ) ^ 20 * (nativeGap001Scale : ℝ) ^ 20) := by
      simp only [nativeIndividualNormalizedMomentCurve,
        nativeConfiguredNormalizedMomentCurve, nativeIndividualMomentCurve,
        nativeSourceBandMomentK, nativeSourceBandAverage]
      rfl
    rw [hu] at hcmp
    have hres : nativeVectorReal (nativeConfiguredSystem 0).result ⟨20, by norm_num⟩ ≤
        (((5 / 2 : ℚ) / ((3 / 50 : ℚ) * nativeGap001Scale)) ^ 20 : ℚ) := by
      change (((nativeGap001Result.getD 20 0 : ℚ)) : ℝ) ≤ _
      exact_mod_cast nativeRefinedChild_result20_le
    have hden : (0 : ℝ) < (3 / 50 : ℝ) ^ 20 * (nativeGap001Scale : ℝ) ^ 20 := by
      have := nativeGap001Scale_pos
      positivity
    have h1 := (div_le_iff₀ hden).1 (hcmp.trans hres)
    refine h1.trans (le_of_eq ?_)
    have hs : (nativeGap001Scale : ℝ) ≠ 0 := by
      have : (0 : ℝ) < nativeGap001Scale := by exact_mod_cast nativeGap001Scale_pos
      exact this.ne'
    push_cast
    field_simp
  have hl : ∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ ≤ ENNReal.ofReal (5 / 2) ^ (20 : ℝ) := by
    have : ∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ = ENNReal.ofReal (∫ ω, f ω ^ (20 : ℝ) ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hpow
        (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hf0 ω) _)]
      apply lintegral_congr
      intro ω
      rw [Real.enorm_eq_ofReal (hf0 ω), ENNReal.ofReal_rpow_of_nonneg (hf0 ω) (by norm_num)]
    rw [this, ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [show ((20 : ℝ)) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact hmoment
  have hp : (eLpNorm' f 20 μ) ^ (20 : ℝ) ≤ ENNReal.ofReal (5 / 2) ^ (20 : ℝ) := by
    rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 20)]
    exact hl
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 20)).mp hp


/-- The lag -1 child in the completed frame has L^20 cap `3`: the gap-one
individual system followed by the one-step frame map. -/
theorem nativeRefinedChild_L20_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    eLpNorm' (cutoffTraceDefect M n (n - 1)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal 3 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let f := fun ω : Cutoff.CutoffSample 2 =>
    modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M (n-1))
      (nativeSourceBandScalar (n-1) 1 1 ω)
  let g := cutoffTraceDefect M n (n-1)
  let eta := nativeSourceFrameEta
  let A := 1+eta
  let C := 8*(1+1/eta)*((11/10:ℝ)*M.gamma*(1:ℝ))^2
  let R := nativeSourceE M.gamma 1
  have hg0 := M.shellPrefix.gamma_pos.le
  have hgz : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have hR : 0 ≤ R := native_source_E_nonneg M.gamma 1 hg0 hgz (by norm_num)
  have hA : 0 ≤ A := by norm_num [A,eta,nativeSourceFrameEta]
  have hC : 0 ≤ C := by dsimp [C,eta,nativeSourceFrameEta]; positivity
  have hfm : AEStronglyMeasurable f μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu (Annealed.sigmaBar M (n-1)) M.nu_pos
      (Annealed.sigmaBar_characterization M (n-1)).1).1.continuous.measurable.comp
        (native_source_band_scalar_measurable (n-1) 1 1)).aestronglyMeasurable
  have hf0 (ω) : 0 ≤ f ω := modelTraceObservable_nonneg (n-1) M.nu (Annealed.sigmaBar M (n-1)) M.nu_pos
    (Annealed.sigmaBar_characterization M (n-1)).1 _
  have hgnonneg (ω) : 0 ≤ g ω := cutoffTraceDefect_nonneg M n (n-1) ω
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M (n-1) 1
  have hlabel : n-1+((1:ℕ):ℤ)=n := by omega
  rw [hlabel] at hratio
  have hE := native_source_E_ge_three_power M.gamma 1 hg0 hgz (by norm_num)
  have hratioR : (Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M (n-1):ℝ) ≤ R :=
    hratio.2.trans (by
      dsimp only [R]
      convert hE using 1
      congr 1
      ring)
  have hpoint (ω) : g ω ≤ R*(A*f ω+C) := by
    have hm := source_cutoff_pathwise_frame_map M (n-1) n (n-1) ω (by omega)
      eta (by norm_num [eta,nativeSourceFrameEta])
    have hgap : (n:ℝ)-((n-1:ℤ):ℝ)=1 := by push_cast; ring
    rw [hgap] at hm
    have he := native_source_band_trace_one M (n-1) 1 ω
    rw [hlabel] at he
    rw [←he] at hm
    simpa only [g,A,f,C,mul_one] using hm.trans
      (mul_le_mul_of_nonneg_right hratioR (add_nonneg (mul_nonneg hA (hf0 ω)) hC))
  have hband := nativeRefinedChild_bandObservable_L20 M h hM hg (n-1)
    (fun j hj => hpast j (by omega)) (hpast (n-1) (by omega))
  have hcap := native_source_affine_L20_cap μ f g hfm hf0 hgnonneg R A C (5/2) hR hA hC
    (by norm_num) hband hpoint
  refine hcap.trans (ENNReal.ofReal_le_ofReal ?_)
  have hden : 1 - (11 / 10 : ℝ) * (2 * ((1 : ℕ) : ℝ) * M.gamma) ≥ 99 / 100 := by
    push_cast; nlinarith
  have hRle : R ≤ 101 / 100 := by
    dsimp only [R, nativeSourceE]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hCle : C ≤ 1 / 100 := by
    dsimp only [C, eta, nativeSourceFrameEta]
    have : (11 / 10 : ℝ) * M.gamma * 1 ≤ 1 / 1000 := by nlinarith
    have h2 : ((11 / 10 : ℝ) * M.gamma * 1) ^ 2 ≤ (1 / 1000) ^ 2 :=
      pow_le_pow_left₀ (by positivity) this 2
    nlinarith
  have hA' : A = 1001 / 1000 := by norm_num [A, eta, nativeSourceFrameEta]
  rw [hA']
  nlinarith

end
end ASDExplicitGamma.Native
