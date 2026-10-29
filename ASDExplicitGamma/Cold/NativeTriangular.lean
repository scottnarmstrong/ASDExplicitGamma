module

public import ASDExplicitGamma.Cold.NativePlateauStep
public import ASDExplicitGamma.Cold.ColdMeanInduction

/-! # Native same-law cold continuation through lag 128 -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Proportionally scaled cold continuation at one actual completed coefficient and true frame.
The cutoff thresholds and recurrence parameters stay at their certified endpoint values. -/
theorem cold_native_triangular_scaled (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hordinary : ordinaryMean M m ≤ ENNReal.ofReal (θ*(coldA:ℝ)))
    (hstrong : strong20 M m ≤ ENNReal.ofReal (θ*(coldS20:ℝ)))
    (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ))) :
    ∀ (j : ℕ), j ≤ 128 → coldNativeMean M m j ≤ θ*(coldMeanAt j:ℝ) := by
  apply cold_mean_table_induction hθ (coldNativeMean_antitone M m)
    (coldNativeMean_zero_le (mul_nonneg hθ.le (by norm_num [coldA])) hordinary)
  intro j hj hprior
  exact cold_native_plateau_step M h hM m hθ.le hθ1 hroot hstrong (r4 := 4) rfl hj hprior

/-- CO-TRIANGULAR-129: the actual ordinary means through lag 128 are bounded by the
kernel-checked producing table, at one fixed completed coefficient/frame. No recurrence,
measurability, local-independence, graph or intermediate mean cap is assumed. The stated root
L2 endpoint is derived by interpolation from the genuine source inputs. -/
theorem cold_triangular_129 (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (hordinary : ordinaryMean M m ≤ ENNReal.ofReal (3/50:ℝ))
    (hstrong : strong20 M m ≤ ENNReal.ofReal (2379/2500:ℝ))
    (hroot : root20 M m ≤ ENNReal.ofReal (2013/10000:ℝ)) :
    ∀ (j : ℕ), j ≤ 128 → (∫ ω, cutoffTraceDefect M m (m+(j:ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ (coldMeanAt j:ℝ) := by
  have hO : ordinaryMean M m ≤ ENNReal.ofReal ((1:ℝ)*(coldA:ℝ)) := by simpa only [one_mul,coldA,Rat.cast_div,Rat.cast_ofNat] using hordinary
  have hS : strong20 M m ≤ ENNReal.ofReal ((1:ℝ)*(coldS20:ℝ)) := by simpa only [one_mul,coldS20,Rat.cast_div,Rat.cast_ofNat] using hstrong
  have hR : root20 M m ≤ ENNReal.ofReal ((1:ℝ)*(coldR20:ℝ)) := by simpa only [one_mul,coldR20,Rat.cast_div,Rat.cast_ofNat] using hroot
  simpa only [one_mul,coldNativeMean,coldNativeTrace] using
    cold_native_triangular_scaled M h hM m (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 1) hO hS hR

end ASDExplicitGamma.Cold
