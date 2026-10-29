module

public import ASDExplicitGamma.Native.HeatActualIndividualProfiles
public import ASDExplicitGamma.Native.HeatIndividualGeneratorPayment

/-! The actual degree-specific individual source row for every configured gap. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Inverse
open scoped ENNReal
noncomputable section

/-- Actual source generator payment for degrees2 through20, with no source-row,
trace-profile, inverse-bank or rare-reserve estimate among the premises. -/
theorem native_source_band_power_generator_le_individual_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153)
    (k : ℕ) (hk : 2 ≤ k) (hk20 : k ≤ 20)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    let height := (nativeConfiguredSystem index).gap
    let row := nativeIndividualRow height k (nativeOld height)
    (∫ ω,nativeSourceBandPowerGeneratorK M h n height t k ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (row.2.1:ℝ)*nativeSourceBandMomentK M n height k t+
      (3/50:ℝ)*(row.1:ℝ)*nativeSourceBandMomentK M n height (k-1) t+
      (3/50:ℝ)^k*(row.2.2:ℝ) := by
  let height := (nativeConfiguredSystem index).gap
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let sourceProbability : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar n height t ω)
  let R := nativeSourceBandRemainder M n height t
  let P := fun ω => (nativeSourceBandHistory M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (nativeSourceBandScalar n height t ω)
  let G := nativeSourceBandPowerGeneratorK M h n height t k
  obtain ⟨hR,hT,hR0,hT0,hRc,h20,h128,hbank⟩ :=
    native_source_band_configured_profiles M h hM hg n hpast hstate index t ht
  have hgap := heat_configured_gap_bounds index
  have hG := native_source_band_power_generatorK_integrable M h hM n height k hgap.1 hk t
  have he := (heat_source_profiles_le_old M.gamma height M.shellPrefix.gamma_pos.le hg
    (by dsimp [height]; omega)).1
  have hk1 : 1 ≤ k := by omega
  have hkCast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by simp only [Nat.cast_sub hk1,Nat.cast_one]
  have hsrc := native_source_band_power_generatorK_exact_ae_le M h hM hg n height hpast hstate t ht.2 k hk hk20
  have hsource : ∀ᵐ ω ∂μ,G ω ≤
      (k:ℝ)*T ω^(k-1)*((nativeOld height).e:ℝ)*
        ((((2*(k:ℝ)-1)*(height:ℝ)+2*((k:ℝ)-1)*(521/1000))*D ω)+
          2*(521/1000)*(P ω*(T ω+4))+
          (1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000))*(P ω^2*(T ω+4))) := by
    filter_upwards [hsrc] with ω hs
    dsimp only at hs
    rw [←hkCast,Real.rpow_natCast] at hs
    have hD0 : 0 ≤ D ω := native_source_model_inverse_trace_nonneg n M.nu
      (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
    have hP0 : 0 ≤ P ω := ENNReal.toReal_nonneg
    have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hkm : 0 ≤ (k:ℝ)-1 := by linarith
    have h2k : 0 ≤ 2*(k:ℝ)-1 := by linarith
    have hinner : 0 ≤
        ((2*(k:ℝ)-1)*(height:ℝ)+2*((k:ℝ)-1)*(521/1000))*D ω+
          2*(521/1000)*(P ω*(T ω+4))+
          (1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000))*(P ω^2*(T ω+4)) := by
      have hT0ω := hT0 ω
      positivity
    have hscale := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he hinner)
      (show 0 ≤ (k:ℝ)*T ω^(k-1) by have hT0ω := hT0 ω; positivity)
    have hs' : G ω ≤ (k:ℝ)*T ω^(k-1)*(nativeSourceRawShellVarianceCap M.gamma height*
        (((2*(k:ℝ)-1)*(height:ℝ)+2*((k:ℝ)-1)*(521/1000))*D ω+
          2*(521/1000)*(P ω*(T ω+4))+
          (1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000))*(P ω^2*(T ω+4)))) := by
      simpa only [T,P,D,G,hkCast] using hs
    simpa only [mul_assoc] using hs'.trans hscale
  have hpay := heat_individual_generator_integral_le_source_row μ index R T P D G
    hR hT hR0 hT0 k hk1 hk20 hRc h20 h128 hG hbank hsource
  simpa only [nativeSourceBandMomentK,nativeSourceBandAverage,Real.rpow_natCast,T,G,μ] using hpay

end
end ASDExplicitGamma.Native
