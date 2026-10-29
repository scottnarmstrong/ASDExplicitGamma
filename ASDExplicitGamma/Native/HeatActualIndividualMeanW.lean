module

public import ASDExplicitGamma.Native.HeatActualIndividualPowerW
public import ASDExplicitGamma.Native.GenericSourceBandMeanHeatW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! The first individual moment row, retaining the augmented constant column. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Inverse
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- The actual first-moment generator fits the same individual producer row.
Every law and bank estimate is supplied internally, including the constant
predecessor coordinate and the complete first-order rare forcing. -/
theorem native_source_band_mean_generator_le_individual_row_W
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
      (3/50:ℝ)*(row.1:ℝ)*nativeSourceBandMomentK_W W M n height 0 t+
      (3/50:ℝ)*(row.2.2:ℝ) := by
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
    native_source_band_configured_profiles_W M h hM hg n hpast hstate index t ht
  have hgap := heat_configured_gap_bounds index
  have hG := native_source_band_mean_generator_integrable_W (W := W) M h hM n height hgap.1 t
  have he := (heat_source_profiles_le_old M.gamma height M.shellPrefix.gamma_pos.le hg
    (by dsimp [height]; omega)).1
  have hsrc := native_source_band_mean_generator_ae_le_W (W := W) M h hM hg n height hpast hstate t ht.2
  have hsource : ∀ᵐ ω ∂μ,G ω ≤ ((nativeOld height).e:ℝ)*
      ((height:ℝ)*D ω+2*(521/1000)*(P ω*(T ω+4))+(1975/1000)*(P ω^2*(T ω+4))) := by
    filter_upwards [hsrc] with ω hs
    have hD0 : 0 ≤ D ω := native_source_model_inverse_trace_nonneg n M.nu
      (Annealed.sigmaBar M n) M.nu_pos (Annealed.sigmaBar_characterization M n).1 _
    have hP0 : 0 ≤ P ω := ENNReal.toReal_nonneg
    have hT0ω := hT0 ω
    exact hs.trans (mul_le_mul_of_nonneg_right he (by positivity))
  have hpay := heat_individual_generator_integral_le_source_row μ index R T P D G
    hR hT hR0 hT0 1 (by norm_num) (by norm_num) hRc h20 h128 hG hbank (by
      simpa only [Nat.cast_one,Nat.sub_self,Nat.cast_zero,pow_zero,one_mul,mul_one,mul_zero,
        zero_mul,add_zero,zero_add,sub_self,show (2:ℝ)-1=1 by norm_num] using hsource)
  simpa only [nativeSourceBandMomentK_W,nativeSourceBandAverage_W,Real.rpow_natCast,T,G,μ,
    Nat.sub_self,pow_one] using hpay

end
end ASDExplicitGamma.Native
