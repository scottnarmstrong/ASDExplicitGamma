module

public import ASDExplicitGamma.Native.GenericSourceChildBandFactors

/-! Sharp finite-pass factors on the simultaneous source path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The three actual norm factors in the source generator obey exactly the
finite-pass minima `d,b*u1,b²*u2`. Only the previous trace cap is an input to
this refinement step; inverse and full-response bank inputs are discharged. -/
theorem native_source_child_band_refined_norms
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j) (height : ℕ)
    (t : ℝ) (ht1 : t ≤ 1)
    (x : ℝ) (hx : 0 ≤ x)
    (htrace : eLpNorm' (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable (n-1) M.nu (Annealed.sigmaBar M n)
        (nativeSourceChildBandScalar n height t ω))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal x) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let σ : ℝ := Annealed.sigmaBar M n
    let X := nativeSourceChildBandScalar n height t
    let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
    let F := fun ω => T ω+4
    let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
    let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
    let f := nativeSourceChildFullResponseCap M.gamma height
    positiveLpNorm μ 20 D ≤ nativeSourceInterpolationD x ∧
    positiveLpNorm μ 20 (fun ω => P ω*F ω) ≤
      nativeSourceB128*nativeSourceInterpolationU1 x f ∧
    positiveLpNorm μ 20 (fun ω => (P ω)^2*F ω) ≤
      nativeSourceB128^2*nativeSourceInterpolationU2 x f := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M n
  let X := nativeSourceChildBandScalar n height t
  let T := fun ω => modelTraceObservable (n-1) M.nu σ (X ω)
  let F := fun ω => T ω+4
  let P := fun ω => (nativeSourceChildBandHistory M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (X ω)
  let f := nativeSourceChildFullResponseCap M.gamma height
  have hTm : AEStronglyMeasurable T μ :=
    ((modelTraceObservable_hasPolynomiallyBoundedC2Derivatives (n-1) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp
        (native_source_child_band_scalar_measurable n height t)).aestronglyMeasurable
  have hPm : AEStronglyMeasurable P μ :=
    (native_source_child_band_history_toReal_measurable M n height t).aestronglyMeasurable
  have hP0 (ω) : 0 ≤ P ω := ENNReal.toReal_nonneg
  have hT0 (ω) : 0 ≤ T ω := modelTraceObservable_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hD0 (ω) : 0 ≤ D ω := native_source_model_inverse_trace_nonneg (n-1) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 _
  have hF0 (ω) : 0 ≤ F ω := add_nonneg (hT0 ω) (by norm_num)
  have hFm : AEStronglyMeasurable F μ := hTm.add aestronglyMeasurable_const
  have hXmeas : Measurable X := native_source_child_band_scalar_measurable n height t
  have hDm : AEStronglyMeasurable D μ :=
    ((bank_inverse_trace_observable_C2 (n-1) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1).1.continuous.measurable.comp hXmeas).aestronglyMeasurable
  have hPcap := native_source_child_band_history_toReal_L128 M h hM hg n height hpast t ht1
  have hPprime : eLpNorm' P 128 μ ≤ ENNReal.ofReal nativeSourceB128 := by
    have he := eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0)
      (by norm_num : (128:ℝ≥0∞)≠⊤) hPm
    rw [he] at hPcap
    exact hPcap
  have hFcap := native_source_child_band_full_response_L128 M h hM hg n height hpast t ht1
  have hFprime : eLpNorm' F 128 μ ≤ ENNReal.ofReal f := by
    have he := eLpNorm_eq_eLpNorm' (by norm_num : (128:ℝ≥0∞)≠0)
      (by norm_num : (128:ℝ≥0∞)≠⊤) hFm
    rw [he] at hFcap
    exact hFcap
  have hDbank : ∀ᵐ ω ∂μ, D ω ≤ 2*P ω :=
    native_source_child_band_inverse_trace_ae_le M h hM hg n height hpast t ht1
  have hDtrace : ∀ᵐ ω ∂μ, D ω ≤ 2+T ω+Real.sqrt (2*T ω) :=
    Filter.Eventually.of_forall fun ω => native_source_model_inverse_trace_le (n-1) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
  have hFF : F = fun ω => 4+T ω := by funext ω; dsimp [F]; ring
  have hf : 0 ≤ f := by have hg0 := M.shellPrefix.gamma_pos.le; dsimp [f,nativeSourceChildFullResponseCap]; positivity
  have hD := native_source_refined_inverse_cap μ P T D hPm hTm
    (Filter.Eventually.of_forall hP0) (Filter.Eventually.of_forall hT0)
    (Filter.Eventually.of_forall hD0) hDbank hDtrace x hx hPprime htrace
  have hProd := native_source_refined_product_caps μ P T F hPm hTm
    (Filter.Eventually.of_forall hT0) hFF x f hx hf hPprime htrace hFprime
  have hd0 : 0 ≤ nativeSourceInterpolationD x := by unfold nativeSourceInterpolationD nativeSourceB128; positivity
  have hu1 : 0 ≤ nativeSourceInterpolationU1 x f := by unfold nativeSourceInterpolationU1; positivity
  have hu2 : 0 ≤ nativeSourceInterpolationU2 x f := by unfold nativeSourceInterpolationU2; positivity
  exact ⟨native_source_real_norm_le_of_prime_cap μ D hDm hD0 _ hd0 hD,
    native_source_real_norm_le_of_prime_cap μ (fun ω => P ω*F ω) (hPm.mul hFm)
      (fun ω => mul_nonneg (hP0 ω) (hF0 ω)) _ (mul_nonneg (by norm_num [nativeSourceB128]) hu1) hProd.1,
    native_source_real_norm_le_of_prime_cap μ (fun ω => (P ω)^2*F ω) (hPm.pow 2 |>.mul hFm)
      (fun ω => mul_nonneg (sq_nonneg (P ω)) (hF0 ω)) _ (mul_nonneg (sq_nonneg _) hu2) hProd.2⟩

end
end ASDExplicitGamma.Native
