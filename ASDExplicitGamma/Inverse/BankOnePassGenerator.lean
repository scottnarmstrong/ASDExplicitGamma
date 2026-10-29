module

public import ASDExplicitGamma.Inverse.BankOnePassLocal
public import ASDExplicitGamma.Inverse.BankHeatIntegrability
public import ASDExplicitGamma.Inverse.BankCovarianceSum
public import ASDExplicitGamma.Gaussian.ShellFrameClock

/-! Source pure-flux generator boundary and its actual-model expectation. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Set Algsuperdiff.Section3 ASDExplicitGamma.Gaussian

/-- The remaining IN-PURE-FLUX-GENERATOR input: the signed physical covariance
trace during each deterministic partial insertion, in the completed k frame.
The factor is the literal unweighted covariance coefficient. This is an input
to helpers, not a theorem or a bank conclusion. -/
def BankPureFluxGeneratorInput (M : ABKModel 2) (h : ℝ) (k : ℤ) : Prop :=
  ∀ (s : ℕ) (_hs : 1 ≤ s ∧ s ≤ 40) (t : ℝ) (_ht : t ∈ Icc (0:ℝ) 1)
    (T : GaussianFactorL2 ℕ →L[ℝ] C(closure (cubeSet (originCube 2 k)),ℝ))
    (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖^2)),
    (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 k))) (ω.1 (k+(s:ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) →
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (1/2:ℝ)*modelCovarianceTrace
        (bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k:ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M k).1) (fun j => T (v j))
        (modelInsertedScalar (closure (cubeSet (originCube 2 k))) (k+(s:ℤ)-1) t ω) ≤
      (q3ModelAmplitude M h (k+(s:ℤ)))^2 /
        (Annealed.sigmaBar M k:ℝ)^2 *
        pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1)) *
        (bankOnePassLocalHistory M k s t ω)^2 *
        bankInverseTrace k (Model.partialInsertedCoefficient M (k+(s:ℤ)-1) t ω).toFun
          (Annealed.sigmaBar M k:ℝ)


/-- Integrating the signed source generator uses the already proved actual
local-history cubic moment. The response and history may be correlated. -/
theorem bank_one_pass_generator_mean_of_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (k : ℤ) (hpast : ∀ n < k, nativeInductionState M h n)
    (hgen : BankPureFluxGeneratorInput M h k)
    (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (T : GaussianFactorL2 ℕ →L[ℝ] C(closure (cubeSet (originCube 2 k)),ℝ))
    (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖^2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 k))) (ω.1 (k+(s:ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) :
    (1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 k))) M (k+(s:ℤ)-1)
      (bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k:ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M k).1) (fun j => T (v j)) t ≤
      2*((q3ModelAmplitude M h (k+(s:ℤ)))^2/(Annealed.sigmaBar M k:ℝ)^2)*
        pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1))*
          (159/100:ℝ)^3 := by
  let K := closure (cubeSet (originCube 2 k))
  let Φ := bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k:ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M k).1
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := bankOnePassLocalHistory M k s t
  let c := 2*((q3ModelAmplitude M h (k+(s:ℤ)))^2/(Annealed.sigmaBar M k:ℝ)^2)*
    pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1))
  let L := fun ω => (1/2:ℝ)*modelCovarianceTrace Φ (fun j => T (v j))
    (modelInsertedScalar K (k+(s:ℤ)-1) t ω)
  have hc : 0 ≤ c := mul_nonneg (by positivity) (pureFlux_covariance_mu_lower _ _).1
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 k)).isCompact_closure
  have hΦ := bank_inverse_trace_observable_C2 k M.nu (Annealed.sigmaBar M k:ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M k).1
  have hL : Integrable L μ := (bank_model_heat_integrable K M h hM ell (k+(s:ℤ)-1) hK
    (modelCovarianceTrace Φ (fun j => T (v j))) (measurable_modelCovarianceTrace Φ hΦ.1 _)
    (polynomial_modelCovarianceTrace _ (summable_sq_norm_gaussianDirections hA T) Φ hΦ) t).const_mul (1/2)
  have hB := bank_one_pass_local_cubic M h hM hg k s t ht.2 hpast
  have hdom : ∀ᵐ ω ∂μ, L ω ≤ c*(B ω)^3 := by
    filter_upwards [hgen s hs t ht T v hA hlaw,
      bank_one_pass_trace_le_local_history M h hM hg k s hs t ht hpast] with ω hω htrace
    exact bank_signed_generator_cubic (by positivity) (pureFlux_covariance_mu_lower _ _).1 hω htrace
  have hh := integral_mono_ae hL (hB.1.const_mul c) hdom
  have hInt : (∫ ω, c*(B ω)^3 ∂μ) = c*(∫ ω, (B ω)^3 ∂μ) := integral_const_mul c _
  rw [hInt] at hh
  have hbound := hh.trans (mul_le_mul_of_nonneg_left hB.2 hc)
  simpa only [L,modelHeatTraceAverage,modelHeatAverage,μ,integral_const_mul,K,Φ,c,B] using hbound

end ASDExplicitGamma.Inverse
