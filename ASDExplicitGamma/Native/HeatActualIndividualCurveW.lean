module

public import ASDExplicitGamma.Native.HeatActualIndividualMeanW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! The full actual individual moment curve, including degrees zero and one. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Gaussian Numerics.Native Inverse Set
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- Actual generator expectation in each augmented moment coordinate. -/
def heatIndividualActualGenerator_W (W : NativeAmp) (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height k : ℕ) (t : ℝ) : ℝ :=
  if k=0 then 0 else if k=1 then
    ∫ ω,nativeSourceBandMeanGenerator_W W M h n height t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure
  else ∫ ω,nativeSourceBandPowerGeneratorK_W W M h n height t k ω ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The actual augmented moment is one on the entire source path. -/
theorem heat_individual_actual_moment_zero_W (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    nativeSourceBandMomentK_W W M n height 0 t = 1 := by
  let sourceProbability : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure :=
    (Cutoff.cutoffSampleLaw M).property
  simp [nativeSourceBandMomentK_W,nativeSourceBandAverage_W]

/-- The degree-one source moment is exactly its physical mean curve. -/
theorem heat_individual_actual_moment_one_W (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceBandMomentK_W W M n height 1 = nativeSourceBandMean_W W M n height := by
  funext t
  simp only [nativeSourceBandMomentK_W,nativeSourceBandAverage_W,nativeSourceBandMean_W,
    Nat.cast_one,Real.rpow_one]

/-- All coordinates have the actual-law heat derivative, with degree zero
fixed and degree one treated by its exact mean generator. -/
theorem heat_individual_actual_moment_heat_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height k : ℕ) (hh : 1 ≤ height) :
    ContinuousOn (nativeSourceBandMomentK_W W M n height k) (Ici 0) ∧
    ∀ t ∈ Ioi (0:ℝ),HasDerivAt (nativeSourceBandMomentK_W W M n height k)
      (heatIndividualActualGenerator_W W M h n height k t) t := by
  by_cases hk0 : k=0
  · subst k
    have hfun : nativeSourceBandMomentK_W W M n height 0 = fun _ => 1 :=
      funext (heat_individual_actual_moment_zero_W M n height)
    rw [hfun]
    exact ⟨continuousOn_const,fun t _ => by
      simpa only [heatIndividualActualGenerator_W,ite_true] using hasDerivAt_const t (1:ℝ)⟩
  by_cases hk1 : k=1
  · subst k
    rw [heat_individual_actual_moment_one_W]
    simpa only [heatIndividualActualGenerator_W,show (1:ℕ)≠0 by decide,ite_false,ite_true] using
      native_source_band_mean_heat_generator_W M h hM n height hh
  · simpa only [heatIndividualActualGenerator_W,hk0,hk1,ite_false] using
      native_source_band_momentK_heat_W M h hM n height k hh (by omega)

/-- Every nonzero actual coordinate obeys its configured RAW row, with all
source bank, profile and forcing bounds discharged. -/
theorem heat_individual_actual_deriv_le_configured_W
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ j<n,nativeInductionState M h j) (hstate : nativeInductionState M h n)
    (index : Fin 153) (i : Fin 21) (hi : i.val ≠ 0)
    (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    let height := (nativeConfiguredSystem index).gap
    deriv (nativeSourceBandMomentK_W W M n height i.val) t ≤
      ((nativeConfiguredSystem index).system.diag.getD i.val 0:ℝ)*nativeSourceBandMomentK_W W M n height i.val t+
      ((nativeConfiguredSystem index).system.subdiag.getD i.val 0:ℝ)*
        ((3/50:ℝ)*((nativeConfiguredSystem index).system.z:ℝ))*nativeSourceBandMomentK_W W M n height (i.val-1) t+
      ((nativeConfiguredSystem index).system.force.getD i.val 0:ℝ)*nativeConfiguredMomentScale index i := by
  let height := (nativeConfiguredSystem index).gap
  have hheat := heat_individual_actual_moment_heat_W (W := W) M h hM n height i.val
    (heat_configured_gap_bounds index).1
  dsimp only
  rw [(hheat.2 t ht.1).deriv]
  apply native_configured_row_of_individual_source index i hi
  by_cases hi1 : i.val=1
  · simpa only [heatIndividualActualGenerator_W,hi,hi1,show (1:ℕ)≠0 by decide,ite_false,ite_true,Nat.sub_self,pow_one] using
      native_source_band_mean_generator_le_individual_row_W M h hM hg n hpast hstate index t ⟨ht.1.le,ht.2.le⟩
  · simpa only [heatIndividualActualGenerator_W,hi,hi1,ite_false] using
      native_source_band_power_generator_le_individual_row_W M h hM hg n hpast hstate index
        i.val (by omega) (by omega) t ⟨ht.1.le,ht.2.le⟩

end
end ASDExplicitGamma.Native
