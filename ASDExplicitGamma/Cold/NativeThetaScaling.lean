module

public import ASDExplicitGamma.Cold.NativeTriangular
public import ASDExplicitGamma.Statements.Theta

/-! # Proportional cold continuation for the exact frozen theta -/

@[expose] public section
noncomputable section
open MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Positivity of the exact frozen proportional factor follows from the genuine model. -/
theorem cold_theta_pos (M : ABKModel 2) : 0 < theta M :=
  div_pos M.shellPrefix.gamma_pos (by norm_num [gammaZero])

/-- The endpoint restriction gives the exact source theta range. -/
theorem cold_theta_le_one (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) : theta M ≤ 1 :=
  (div_le_one (by norm_num [gammaZero] : (0:ℝ) < gammaZero)).mpr hγ

/-- CO-THETA-SCALING: the actual same-label ordinary means are at most theta times the
certified endpoint cap at every lag through 128. Thresholds and recurrence parameters are
fixed at their endpoint values; this theorem does not reround scaled numerical inputs. -/
theorem cold_theta_scaling (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (hγ : M.gamma ≤ gammaZero)
    (hordinary : ordinaryMean M m ≤ ENNReal.ofReal ((3/50:ℝ)*theta M))
    (hstrong : strong20 M m ≤ ENNReal.ofReal ((2379/2500:ℝ)*theta M))
    (hroot : root20 M m ≤ ENNReal.ofReal ((2013/10000:ℝ)*theta M)) :
    ∀ (j : ℕ), j ≤ 128 → (∫ ω, cutoffTraceDefect M m (m+(j:ℤ)) ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ theta M*(coldMeanAt j:ℝ) := by
  have hO : ordinaryMean M m ≤ ENNReal.ofReal (theta M*(coldA:ℝ)) := by
    simpa only [coldA,Rat.cast_div,Rat.cast_ofNat,mul_comm] using hordinary
  have hS : strong20 M m ≤ ENNReal.ofReal (theta M*(coldS20:ℝ)) := by
    simpa only [coldS20,Rat.cast_div,Rat.cast_ofNat,mul_comm] using hstrong
  have hR : root20 M m ≤ ENNReal.ofReal (theta M*(coldR20:ℝ)) := by
    simpa only [coldR20,Rat.cast_div,Rat.cast_ofNat,mul_comm] using hroot
  exact cold_native_triangular_scaled M h hM m (cold_theta_pos M) (cold_theta_le_one M hγ) hO hS hR

end ASDExplicitGamma.Cold
