module

public import ASDExplicitGamma.Cold.NativeMomentSystem
public import ASDExplicitGamma.Cold.MomentSystemFluctuation
public import ASDExplicitGamma.Cold.ColdScalingAlgebra

/-! # Actual native positive-fluctuation caps at every permitted history lag -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Native positive-fluctuation caps use only the earlier mean at k and earlier inputs
of the moment table. The k=ell case is its raw nonnegative trace bound. -/
theorem cold_native_fluctuation_table (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    {n k ell : ℕ} (hn : n ≤ 128) (hk : k < n) (hkle : k ≤ ell)
    (hmean : ∀ i < n, coldNativeMean M m i ≤ θ*(coldMeanAt i:ℝ)) :
    lpNorm (fun ω => max (coldNativeTrace M m ell ω-θ*(coldMeanAt k:ℝ)) 0) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ coldCenteredMomentCap (θ*(coldMomentAt k:ℝ)) (ell-k) := by
  have hkn : k ≤ 128 := by omega
  have hs := cold_table_nonneg k (List.mem_range.mpr (by omega))
  have hMomentNonneg : 0 ≤ θ*(coldMomentAt k:ℝ) := mul_nonneg hθ (Rat.cast_nonneg.mpr hs.2)
  have hD : 0 ≤ θ*(coldMeanAt k:ℝ) := mul_nonneg hθ (Rat.cast_nonneg.mpr hs.1)
  have hcap := cold_native_moment_table M h hM m hθ hroot hkn
    (fun i hi => hmean i (hi.trans hk))
  by_cases hke : k = ell
  · subst ell
    have hm := coldNativeTrace_memLp hroot k
    have hmono : lpNorm (fun ω => max (coldNativeTrace M m k ω-θ*(coldMeanAt k:ℝ)) 0) 20
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ lpNorm (coldNativeTrace M m k) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
      apply cold_lpNorm_mono_ae hm
      apply Filter.Eventually.of_forall
      intro ω
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),
        abs_of_nonneg (coldNativeTrace_nonneg M m k ω)]
      exact max_le (sub_le_self _ hD) (coldNativeTrace_nonneg M m k ω)
    simpa only [Nat.sub_self,coldCenteredMomentCap,ite_true] using hmono.trans hcap
  · exact (coldNativeMomentSystem M h hM m hroot).positive_fluctuation
      (by omega) hMomentNonneg hcap (hmean k hk)

end ASDExplicitGamma.Cold
