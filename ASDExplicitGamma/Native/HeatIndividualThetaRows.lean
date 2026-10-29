module

public import ASDExplicitGamma.Native.HeatIndividualThetaBill
public import ASDExplicitGamma.Native.HeatIndividualGeneratorPayment
public import ASDExplicitGamma.Native.HeatIndividualThetaProfiles
public import ASDExplicitGamma.Native.HeatActualIndividualMeanW
public import ASDExplicitGamma.Native.HeatActualIndividualPowerW

/-! Theta-scaled physical source-row integration into the selected individual coefficients,
and the theta-scaled actual generator rows of the individual source band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory Homogenization Algsuperdiff.Section3 Gaussian Inverse
open scoped ENNReal
noncomputable section

theorem heat_individual_generator_integral_le_source_row_theta
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (index : Fin 153) (R T P D G : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ z,0 ≤ R z) (hT0 : ∀ z,0 ≤ T z)
    (k : ℕ) (hk : 1 ≤ k) (hk20 : k ≤ 20)
    (τ e' : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (he' : 0 ≤ e')
    (hee : e' ≤ τ * ((nativeOld (nativeConfiguredSystem index).gap).e : ℝ))
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal (nativeEps:ℝ))
    (h20 : eLpNorm' T 20 μ ≤
      ENNReal.ofReal (τ * ((nativeOld (nativeConfiguredSystem index).gap).x:ℝ)))
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal ((nativeOld (nativeConfiguredSystem index).gap).f:ℝ))
    (hG : Integrable G μ)
    (hbank : ∀ᵐ z ∂μ,0 ≤ P z ∧ D z ≤ 2*P z ∧ P z ≤ (nativeB:ℝ)+R z)
    (hsource : ∀ᵐ z ∂μ,G z ≤
      (k:ℝ)*T z^(k-1)*e'*
        ((((2*(k:ℝ)-1)*((nativeConfiguredSystem index).gap:ℝ)+2*((k:ℝ)-1)*(521/1000))*D z)+
          2*(521/1000)*(P z*(T z+4))+
          (1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000))*(P z^2*(T z+4)))) :
    let row := nativeIndividualRow (nativeConfiguredSystem index).gap k
      (nativeOld (nativeConfiguredSystem index).gap)
    (∫ z,G z ∂μ) ≤ (row.2.1:ℝ)*(∫ z,T z^k ∂μ)+
      (3/50:ℝ)*τ*(row.1:ℝ)*(∫ z,T z^(k-1) ∂μ)+((3/50:ℝ)*τ)^k*(row.2.2:ℝ) := by
  have hbill := heat_configured_individual_bill_integral_theta_le μ index R T hR hT hR0 hT0
    k hk hk20 τ e' hτ hτ1 he' hee hRc h20 h128
  let height := (nativeConfiguredSystem index).gap
  let a : ℝ := (2*(k:ℝ)-1)*(height:ℝ)+2*((k:ℝ)-1)*(521/1000)
  let c : ℝ := 1975/1000+2*((k-1:ℕ):ℝ)*(1565/1000)
  let d : ℝ := 2*(height:ℝ)+4*((k:ℝ)-1)*((height:ℝ)+521/1000)
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 ≤ (k:ℝ)-1 := sub_nonneg.mpr hkR
  have h2k : 0 ≤ 2*(k:ℝ)-1 := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hd : 2*a=d := by dsimp [a,d]; ring
  have hpoint : ∀ᵐ z ∂μ,G z ≤ heatIndividualSourceBill k e' d (521/1000) c nativeB (T z) (R z) := by
    filter_upwards [hsource,hbank] with z hs hb
    have hp := heat_individual_source_le_bill k hk e' a (521/1000) c nativeB
      (T z) (P z) (D z) (R z) he' ha (by norm_num) (by dsimp [c]; positivity)
      (hT0 z) hb.1 hb.2.1 hb.2.2
    rw [hd] at hp
    apply hs.trans
    convert hp using 1 <;> ring
  have hI := (integral_mono_ae hG hbill.1 hpoint).trans hbill.2
  dsimp only at hI ⊢
  simp only [nativeA, Rat.cast_div, Rat.cast_ofNat] at hI
  have e1 : ((3/50:ℝ)*τ)^k = (3/50:ℝ)^k * τ^k := by rw [mul_pow]
  linarith [hI]

variable {W : NativeAmp}

/-- Actual source generator payment for degrees2 through20, with no source-row,
trace-profile, inverse-bank or rare-reserve estimate among the premises. -/
theorem native_source_band_power_generator_le_individual_row_theta_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153)
    (k : ℕ) (hk : 2 ≤ k) (hk20 : k ≤ 20)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    let height := (nativeConfiguredSystem index).gap
    let row := nativeIndividualRow height k (nativeOld height)
    (∫ ω,nativeSourceBandPowerGeneratorK_W W M h n height t k ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (row.2.1:ℝ)*nativeSourceBandMomentK_W W M n height k t+
      (3/50:ℝ)*theta M*(row.1:ℝ)*nativeSourceBandMomentK_W W M n height (k-1) t+
      ((3/50:ℝ)*theta M)^k*(row.2.2:ℝ) := by
  let height := (nativeConfiguredSystem index).gap
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let sourceProbability : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)
  let R := nativeSourceBandRemainder_W W M n height t
  let P := fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (nativeSourceBandScalar_W W n height t ω)
  let G := nativeSourceBandPowerGeneratorK_W W M h n height t k
  obtain ⟨hR,hT,hR0,hT0,hRc,h20,h128,hbank⟩ :=
    native_source_band_configured_profiles_theta_W M h hM hg n hpast hstate index t ht
  have hgap := heat_configured_gap_bounds index
  have hG := native_source_band_power_generatorK_integrable_W (W := W) M h hM n height k hgap.1 hk t
  have he : nativeSourceRawShellVarianceCap M.gamma height ≤ theta M * ((nativeOld height).e:ℝ) := by
    have := heat_source_variance_le_theta_old M.gamma height M.shellPrefix.gamma_pos.le hg
      (by dsimp [height]; omega)
    have hθ : M.gamma / (17/50000 : ℝ) = theta M := by unfold theta gammaZero; norm_num
    rwa [hθ] at this
  have hk1 : 1 ≤ k := by omega
  have hkCast : ((k-1:ℕ):ℝ)=(k:ℝ)-1 := by simp only [Nat.cast_sub hk1,Nat.cast_one]
  have hsrc := native_source_band_power_generatorK_exact_ae_le_W (W := W) M h hM hg n height hpast hstate t ht.2 k hk hk20
  have hsource : ∀ᵐ ω ∂μ,G ω ≤
      (k:ℝ)*T ω^(k-1)*(nativeSourceRawShellVarianceCap M.gamma height)*
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
    simpa only [mul_assoc] using hs'
  have hpay := heat_individual_generator_integral_le_source_row_theta μ index R T P D G
    hR hT hR0 hT0 k hk1 hk20 (theta M) _ (theta_pos_le_one M hg).1 (theta_pos_le_one M hg).2 (by unfold nativeSourceRawShellVarianceCap; have := M.shellPrefix.gamma_pos.le; positivity) he hRc h20 h128 hG hbank hsource
  simpa only [nativeSourceBandMomentK_W,nativeSourceBandAverage_W,Real.rpow_natCast,T,G,μ] using hpay


/-- The actual first-moment generator fits the same individual producer row.
Every law and bank estimate is supplied internally, including the constant
predecessor coordinate and the complete first-order rare forcing. -/
theorem native_source_band_mean_generator_le_individual_row_theta_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j)
    (hstate : nativeInductionState M h n) (index : Fin 153)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    let height := (nativeConfiguredSystem index).gap
    let row := nativeIndividualRow height 1 (nativeOld height)
    (∫ ω,nativeSourceBandMeanGenerator_W W M h n height t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (row.2.1:ℝ)*nativeSourceBandMomentK_W W M n height 1 t+
      (3/50:ℝ)*theta M*(row.1:ℝ)*nativeSourceBandMomentK_W W M n height 0 t+
      ((3/50:ℝ)*theta M)*(row.2.2:ℝ) := by
  let height := (nativeConfiguredSystem index).gap
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let sourceProbability : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let T := fun ω => modelTraceObservable n M.nu (Annealed.sigmaBar M n) (nativeSourceBandScalar_W W n height t ω)
  let R := nativeSourceBandRemainder_W W M n height t
  let P := fun ω => (nativeSourceBandHistory_W W M n height t ω).toReal
  let D := fun ω => bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (nativeSourceBandScalar_W W n height t ω)
  let G := nativeSourceBandMeanGenerator_W W M h n height t
  obtain ⟨hR,hT,hR0,hT0,hRc,h20,h128,hbank⟩ :=
    native_source_band_configured_profiles_theta_W M h hM hg n hpast hstate index t ht
  have hgap := heat_configured_gap_bounds index
  have hG := native_source_band_mean_generator_integrable_W (W := W) M h hM n height hgap.1 t
  have he : nativeSourceRawShellVarianceCap M.gamma height ≤ theta M * ((nativeOld height).e:ℝ) := by
    have := heat_source_variance_le_theta_old M.gamma height M.shellPrefix.gamma_pos.le hg
      (by dsimp [height]; omega)
    have hθ : M.gamma / (17/50000 : ℝ) = theta M := by unfold theta gammaZero; norm_num
    rwa [hθ] at this
  have hsrc := native_source_band_mean_generator_ae_le_W (W := W) M h hM hg n height hpast hstate t ht.2
  have hsource : ∀ᵐ ω ∂μ,G ω ≤ (nativeSourceRawShellVarianceCap M.gamma height)*
      ((height:ℝ)*D ω+2*(521/1000)*(P ω*(T ω+4))+(1975/1000)*(P ω^2*(T ω+4))) := by
    filter_upwards [hsrc] with ω hs
    have hD0 : 0 ≤ D ω := native_source_model_inverse_trace_nonneg n M.nu
      (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
    have hP0 : 0 ≤ P ω := ENNReal.toReal_nonneg
    have hT0ω := hT0 ω
    exact hs
  have hpay := heat_individual_generator_integral_le_source_row_theta μ index R T P D G
    hR hT hR0 hT0 1 (by norm_num) (by norm_num) (theta M) _ (theta_pos_le_one M hg).1 (theta_pos_le_one M hg).2 (by unfold nativeSourceRawShellVarianceCap; have := M.shellPrefix.gamma_pos.le; positivity) he hRc h20 h128 hG hbank (by
      simpa only [Nat.cast_one,Nat.sub_self,Nat.cast_zero,pow_zero,one_mul,mul_one,mul_zero,
        zero_mul,add_zero,zero_add,sub_self,show (2:ℝ)-1=1 by norm_num] using hsource)
  simpa only [nativeSourceBandMomentK_W,nativeSourceBandAverage_W,Real.rpow_natCast,T,G,μ,
    Nat.sub_self,pow_one] using hpay


end
end ASDExplicitGamma.Native
