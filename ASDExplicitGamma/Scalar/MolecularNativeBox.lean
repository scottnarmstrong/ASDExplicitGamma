module

public import ASDExplicitGamma.Scalar.MolecularTraceMoments
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Numerics.Native.StartupBounds

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- Exact source ratio C20 for the strong and buffered molecular histories. -/
noncomputable def molecularHistoryFactor : ℝ :=
  (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) / (1 - (3 : ℝ) ^ (-(3 / 20 : ℝ)))

private theorem molecular_history_le_of_uniform (R : ℝ) (hR : 0 ≤ R)
    (f : ℕ → ℝ≥0∞) (hf : ∀ r, f r ≤ ENNReal.ofReal R) :
    ENNReal.ofReal (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))) *
      (∑' r : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-(3 / 20 : ℝ) * r)) * f r) ≤
        ENNReal.ofReal (molecularHistoryFactor * R) := by
  let a : ℝ := (3 : ℝ) ^ (-(1 / 4 : ℝ))
  let b : ℝ := (3 : ℝ) ^ (-(3 / 20 : ℝ))
  have ha : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hw (r : ℕ) : (3 : ℝ) ^ (-(3 / 20 : ℝ) * r) = b ^ r := by
    rw [Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  have hs : Summable (fun r : ℕ => b ^ r * R) := (summable_geometric_of_lt_one hb0 hb1).mul_right R
  have he : (∑' r : ℕ, b ^ r * R) = (1 - b)⁻¹ * R := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hb0 hb1]
  calc
    _ ≤ ENNReal.ofReal (1 - a) * ∑' r : ℕ, ENNReal.ofReal (b ^ r * R) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le : (0 : ℝ≥0∞) ≤ _)
      apply ENNReal.tsum_le_tsum
      intro r
      rw [hw, ENNReal.ofReal_mul (pow_nonneg hb0 r)]
      exact mul_le_mul_of_nonneg_left (hf r) (zero_le : (0 : ℝ≥0∞) ≤ _)
    _ = ENNReal.ofReal ((1 - a) * ((1 - b)⁻¹ * R)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => mul_nonneg (pow_nonneg hb0 r) hR) hs,
        he, ← ENNReal.ofReal_mul (sub_nonneg.mpr ha.le)]
    _ = _ := by
      congr 1
      dsimp [molecularHistoryFactor, a, b]
      ring

/-- The frozen singleton L20 coordinate has the molecular bound. -/
theorem root20_molecular (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ) :
    root20 M n ≤ ENNReal.ofReal ((shellVarianceSum h M.gamma n / M.nu ^ 2) ^ 2 / 2 +
      78 * (shellVarianceSum h M.gamma n / M.nu ^ 2)) :=
  cutoffTraceDefect_L20_molecular M h hM n n

/-- The frozen ordinary mean coordinate has its sharper molecular bound. -/
theorem ordinaryMean_molecular (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ) :
    ordinaryMean M n ≤ ENNReal.ofReal ((shellVarianceSum h M.gamma n / M.nu ^ 2) ^ 2 / 2 +
      2 * (shellVarianceSum h M.gamma n / M.nu ^ 2)) :=
  cutoffTraceDefect_mean_molecular M h hM n n

/-- The frozen buffered mean has the same completed-law molecular bound. -/
theorem bufferMean_molecular (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ) :
    bufferMean M n ≤ ENNReal.ofReal ((shellVarianceSum h M.gamma n / M.nu ^ 2) ^ 2 / 2 +
      2 * (shellVarianceSum h M.gamma n / M.nu ^ 2)) :=
  cutoffTraceDefect_mean_molecular M h hM n (n - 40)

/-- The frozen strong mixed history obeys the exact C20 molecular bound. -/
theorem strong20_molecular (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ) :
    strong20 M n ≤ ENNReal.ofReal (molecularHistoryFactor *
      ((shellVarianceSum h M.gamma n / M.nu ^ 2) ^ 2 / 2 +
        78 * (shellVarianceSum h M.gamma n / M.nu ^ 2))) := by
  have hB : 0 ≤ shellVarianceSum h M.gamma n :=
    ge_of_tendsto (ASDExplicitGamma.Model.cutoffPartialStream_variance_tendsto M h n)
      (Filter.Eventually.of_forall fun N => (ASDExplicitGamma.Model.cutoffPartialVariance M h n N).coe_nonneg)
  exact molecular_history_le_of_uniform _ (by positivity)
    (fun r => eLpNorm (cutoffTraceDefect M n (n - r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure)
    (fun r => cutoffTraceDefect_L20_molecular M h hM n (n - r))

/-- The actual mixed buffer-40 history has the same exact C20 bound. -/
theorem buffer40History_molecular (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ) :
    buffer40History M n ≤ ENNReal.ofReal (molecularHistoryFactor *
      ((shellVarianceSum h M.gamma n / M.nu ^ 2) ^ 2 / 2 +
        78 * (shellVarianceSum h M.gamma n / M.nu ^ 2))) := by
  have hB : 0 ≤ shellVarianceSum h M.gamma n :=
    ge_of_tendsto (ASDExplicitGamma.Model.cutoffPartialStream_variance_tendsto M h n)
      (Filter.Eventually.of_forall fun N => (ASDExplicitGamma.Model.cutoffPartialVariance M h n N).coe_nonneg)
  exact molecular_history_le_of_uniform _ (by positivity)
    (fun r => eLpNorm (cutoffTraceDefect M n (n - 40 - r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure)
    (fun r => cutoffTraceDefect_L20_molecular M h hM n (n - 40 - r))

end ASDExplicitGamma.Scalar
