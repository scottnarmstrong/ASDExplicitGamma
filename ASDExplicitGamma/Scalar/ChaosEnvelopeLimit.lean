module

public import ASDExplicitGamma.Scalar.ChaosBilinearLimit
public import ASDExplicitGamma.Scalar.ChaosBilinearMoments
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated convergence of both genuine Gaussian Hilbert-envelope moments. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

local instance instEnvelopeLimitGaussianProbability : IsProbabilityMeasure Gaussian.standardGaussianInfinitePi := by
  unfold Gaussian.standardGaussianInfinitePi
  infer_instance

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The infinite quadratic envelope is measurable under the actual Gaussian realization. -/
theorem measurable_gaussian_hilbert_envelope (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    Measurable (gaussianHilbertEnvelope m B v hA) := by
  have hc : Continuous (fun x : V => ‖m+(B x x-gaussianBilinearTrace B v)‖^2) := by fun_prop
  exact hc.measurable.comp (Gaussian.stronglyMeasurable_gaussianSeriesLimit v hA).measurable

variable [CompleteSpace W]

/-- Both moments needed for the source comparison converge from the actual finite cutoffs. -/
theorem gaussian_hilbert_envelope_moment_limits (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (hA : Summable (fun i => ‖v i‖^2)) :
    let Y := gaussianHilbertEnvelope m B v hA
    let Yn := fun k omega => ‖m+gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega‖^2
    Integrable Y Gaussian.standardGaussianInfinitePi ∧
    Integrable (fun omega => (Y omega)^2) Gaussian.standardGaussianInfinitePi ∧
    Tendsto (fun k => ∫ omega,Yn k omega ∂Gaussian.standardGaussianInfinitePi) atTop
      (nhds (∫ omega,Y omega ∂Gaussian.standardGaussianInfinitePi)) ∧
    Tendsto (fun k => ∫ omega,(Yn k omega)^2 ∂Gaussian.standardGaussianInfinitePi) atTop
      (nhds (∫ omega,(Y omega)^2 ∂Gaussian.standardGaussianInfinitePi)) := by
  let mu := Gaussian.standardGaussianInfinitePi
  let Y := gaussianHilbertEnvelope m B v hA
  let Yn := fun k omega => ‖m+gaussianBilinearPartial B v (Gaussian.gaussianFastIndex hA k) omega‖^2
  let Z := gaussianBilinearMajorant m B v hA
  have hZ4 : MemLp Z 4 mu := memLp_gaussian_bilinear_majorant m B v hA
  have hZ2 : MemLp Z 2 mu := hZ4.mono_exponent (by norm_num)
  have hZi2 : Integrable (fun omega => (Z omega)^2) mu := by
    have h := hZ2.integrable_norm_pow (by decide : (2:ℕ)≠0)
    simpa only [Real.norm_eq_abs,sq_abs] using h
  have hZi4 : Integrable (fun omega => (Z omega)^4) mu := by
    have h := hZ4.integrable_norm_pow (by decide : (4:ℕ)≠0)
    simpa only [Real.norm_eq_abs,show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs] using h
  have hconv : ∀ᵐ omega ∂mu,Tendsto (fun k => Yn k omega) atTop (nhds (Y omega)) :=
    ae_gaussian_hilbert_envelope_partial_tendsto m B v hA
  have hpartial : ∀ᵐ omega ∂mu,∀ k,Yn k omega≤(Z omega)^2 := by
    filter_upwards [ae_gaussian_bilinear_partial_le_majorant m B v hA] with omega hb
    intro k
    exact pow_le_pow_left₀ (norm_nonneg _) (hb k) 2
  have hY0 (omega) : 0≤Y omega := sq_nonneg _
  have hYn0 (k omega) : 0≤Yn k omega := sq_nonneg _
  have hYbound : ∀ᵐ omega ∂mu,Y omega≤(Z omega)^2 := by
    filter_upwards [hconv,hpartial] with omega hc hb
    exact le_of_tendsto (hc) (Eventually.of_forall hb)
  have hYmeas : Measurable Y := measurable_gaussian_hilbert_envelope m B v hA
  have hYint : Integrable Y mu := hZi2.mono' hYmeas.aestronglyMeasurable (hYbound.mono (fun omega hb => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hY0 omega)]
    exact hb))
  have hYint2 : Integrable (fun omega => (Y omega)^2) mu :=
    hZi4.mono' (hYmeas.pow_const 2).aestronglyMeasurable (hYbound.mono (fun omega hb => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (hY0 omega) hb 2
      simpa only [← pow_mul,show (2*2:ℕ)=4 by rfl] using h))
  refine ⟨hYint,hYint2,?_,?_⟩
  · apply tendsto_integral_of_dominated_convergence (fun omega => (Z omega)^2)
      (fun k => (gaussian_bilinear_partial_moment_bound m B v _).1.aestronglyMeasurable) hZi2
    · intro k
      filter_upwards [hpartial] with omega hb
      rw [Real.norm_eq_abs,abs_of_nonneg (hYn0 k omega)]
      exact hb k
    · exact hconv
  · apply tendsto_integral_of_dominated_convergence (fun omega => (Z omega)^4)
      (fun k => (gaussian_bilinear_partial_moment_bound m B v _).2.1.aestronglyMeasurable) hZi4
    · intro k
      filter_upwards [hpartial] with omega hb
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (hYn0 k omega) (hb k) 2
      simpa only [Yn,← pow_mul,show (2*2:ℕ)=4 by rfl] using h
    · filter_upwards [hconv] with omega hc
      exact hc.pow 2

end ASDExplicitGamma.Scalar
