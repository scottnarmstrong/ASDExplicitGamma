module

public import ASDExplicitGamma.Inverse.FullResponsePhysicalWaveMoments
public import ASDExplicitGamma.Inverse.PhysicalGaussianCorrelatedSeries

/-! The existing correlated density series, extended to the terminal endpoint. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Actual correlated reset-wave/density Holder at N≥l-1, using density order p. -/
theorem full_response_reset_wave_density_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N)
    (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (hk : ℕ × ℕ) (e : Fin 3) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let W := physicalResetWave A Q N H0 a c weights hk
    let Y := resetDensityExcess A Q H0 τ (waveGateEta t) q T 4 hk e
    eLpNorm (fun ω => W ω*Real.sqrt (Y ω)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (40*(2*p+2)*(3:ℝ)^(4*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
        Real.sqrt (densityPEEnvelope q 4 p T (resetDensityDepth H0 hk e))) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let W := physicalResetWave A Q N H0 a c weights hk
  let Y := resetDensityExcess A Q H0 τ (waveGateEta t) q T 4 hk e
  let B := 40*(2*p+2)*(3:ℝ)^(4*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))
  let C := densityPEEnvelope q 4 p T (resetDensityDepth H0 hk e)
  have hY := q3_reset_density_bounds A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor hraw hpast
    T hT hcut 4 (Or.inr rfl) p hp hp256 hk e
  have hW := full_response_reset_wave_Lp A h hA Q N hQN H0 hH hpast a c weights hw hk (2*p) (by linarith only [hp])
  have hh := physical_wave_sqrt_density_holder μ W Y
    (physical_reset_wave_measurable A Q N H0 a c weights hk).aestronglyMeasurable hY.1.aestronglyMeasurable
    (reset_density_excess_nonneg A Q H0 τ (waveGateEta t) q T 4 hk e) p C (by linarith only [hp])
    (density_PE_envelope_nonneg q 4 p T (by linarith only [hp]) _) hY.2.1
  apply (hh.trans (mul_le_mul_left hW (ENNReal.ofReal (Real.sqrt C)))).trans_eq
  rw [mul_comm (ENNReal.ofReal B),← ENNReal.ofReal_mul (Real.sqrt_nonneg C)]
  congr 1
  ring


/-- The unchanged finite-resolution and countable-series payment. -/
theorem full_response_correlated_density_term_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N)
    (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (S : ℝ) (hS : 0 ≤ S) (j : Fin 2) (hk : ℕ × ℕ) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let F := physicalCorrelatedDensityTerm A Q N H0 τ (waveGateEta t) q T S a c weights j hk
    Measurable F ∧ eLpNorm F (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (40*(2*p+2)*resetDensityBudget4 q p T A.gamma S (H0-38) j hk) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let Y := fun e : Fin 3 => resetDensityExcess A Q H0 τ (waveGateEta t) q T 4 hk e
  let W := physicalResetWave A Q N H0 a c weights hk
  let u := (S+1)*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)^j.val
  let b := 40*(2*p+2)*(3:ℝ)^(4*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hmeas : Measurable (physicalCorrelatedDensityTerm A Q N H0 τ (waveGateEta t) q T S a c weights j hk) :=
    measurable_const.mul (Finset.measurable_sum _ (fun e _ =>
      (physical_reset_wave_measurable A Q N H0 a c weights hk).mul
        (Real.continuous_sqrt.measurable.comp (q3_reset_density_bounds A h hA hg Q H0 hH τ hτ t q hq0 hq hfloor hraw hpast T hT hcut 4 (Or.inr rfl) p hp hp256 hk e).1)))
  refine ⟨hmeas,?_⟩
  have hn (e : Fin 3) := full_response_reset_wave_density_Lp A h hA hg Q N hQN H0 hH τ hτ t q hq0 hq hfloor
    hraw hpast T hT hcut a c weights hw hk e p hp hp256
  have hs := finite_density_sum_Lp μ (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (fun e ω => W ω*Real.sqrt (Y e ω)) (fun _ => 1)
    (fun e => b*Real.sqrt (densityPEEnvelope q 4 p T (resetDensityDepth H0 hk e)))
    (fun _ => by norm_num) (fun _ => mul_nonneg hb (Real.sqrt_nonneg _)) hn
  simp only [one_mul] at hs
  have he : physicalCorrelatedDensityTerm A Q N H0 τ (waveGateEta t) q T S a c weights j hk =
      u • (fun ω => ∑ e : Fin 3, W ω*Real.sqrt (Y e ω)) := by funext ω; rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hu]
  apply (mul_le_mul_of_nonneg_left hs (zero_le : (0:ℝ≥0∞) ≤ _)).trans
  rw [← ENNReal.ofReal_mul hu,← Finset.mul_sum]
  apply ENNReal.ofReal_le_ofReal
  have hr := reset_density_PE_sqrt_resolution_sum q 4 p T (by linarith only [hp]) H0 hk
  rw [← mul_assoc]
  apply (mul_le_mul_of_nonneg_left hr (mul_nonneg hu hb)).trans_eq
  unfold resetDensityBudget4
  dsimp only [u,b]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hex : -densityPERate 4 i*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1)/2 =
      -(densityPERate 4 i/2)*((localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)+1) := by ring
  rw [hex]
  ring

/-- Complete actual correlated error; all deterministic heights are summed
before the root height is selected. The retained source D4 budget is exact. -/
theorem full_response_correlated_density_series_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N)
    (H0 : ℕ) (hH : 333 ≤ H0) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) (S : ℝ) (hS : 0 ≤ S) (j : Fin 2) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let F := physicalCorrelatedDensityTerm A Q N H0 τ (waveGateEta t) q T S a c weights j
    (∀ᵐ ω ∂μ, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (40*(2*p+2)*(if j=0 then densityD40 q p T A.gamma S (H0-38)
          else densityD41 q p T A.gamma S (H0-38))) := by
  have hb (hk : ℕ × ℕ) := full_response_correlated_density_term_Lp A h hA hg Q N hQN H0 hH τ hτ t q hq0 hq hfloor
    hraw hpast T hT hcut a c weights hw p hp hp256 S hS j hk
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw A).toMeasure (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (physicalCorrelatedDensityTerm A Q N H0 τ (waveGateEta t) q T S a c weights j)
    (fun hk => (hb hk).1)
    (fun hk => 40*(2*p+2)*resetDensityBudget4 q p T A.gamma S (H0-38) j hk)
    (fun hk => mul_nonneg (by positivity) (reset_density_budget4_nonneg q p T A.gamma S hS _ j hk))
    _ ((reset_density_budget4_hasSum q p T A.gamma S hg (H0-38) j).mul_left (40*(2*p+2)))
    (fun hk => (hb hk).2)

end
end ASDExplicitGamma.Inverse
