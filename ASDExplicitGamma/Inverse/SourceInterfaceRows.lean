module

public import ASDExplicitGamma.Native.SourceSmallerGammaInterface

/-! The OLD row extracted from the completed-law conclusion. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Native ASDExplicitGamma.Numerics.Native
open scoped ENNReal

/-- The OLD depth-four mean row consumed by Part B. -/
def inSourceA4 : ℚ :=
  8392611373095084661337932723209 / 10^32

/-- The OLD depth-five mean row consumed by Part B. -/
def inSourceA5 : ℚ :=
  4441091003104432097305984305313 / (5 * 10^31)

/-- The retained completed depth-five inverse row, kept as the producer's
exact rational output. -/
def inSourceXi5Pre : ℚ := nativeSource5Result.2

private theorem nativeCompletedMeanRow_zero :
    nativeCompletedMeanRows.getD 0 0 = (3 / 50 : ℚ) := by
  norm_num [nativeCompletedMeanRows, nativeSource0Result]

private theorem nativeCompletedMeanRow_four_le :
    nativeCompletedMeanRows.getD 4 0 ≤ inSourceA4 := by
  have hrow : nativeCompletedMeanRows.getD 4 0 = nativeSource4Result.1 := by
    simp [nativeCompletedMeanRows]
  have hcap := nativeSource4_caps.1
  have hnum : (20835891731 / 250000000000 : ℚ) ≤ inSourceA4 := by
    norm_num [inSourceA4]
  rw [hrow]
  exact hcap.trans hnum

private theorem nativeCompletedMeanRow_five_le :
    nativeCompletedMeanRows.getD 5 0 ≤ inSourceA5 := by
  have hrow : nativeCompletedMeanRows.getD 5 0 = nativeSource5Result.1 := by
    simp [nativeCompletedMeanRows]
  have hcap := nativeSource5_caps.1
  have hnum : (11028794583 / 125000000000 : ℚ) ≤ inSourceA5 := by
    norm_num [inSourceA5]
  rw [hrow]
  exact hcap.trans hnum

private theorem nativeCompletedWeakRow_five_eq :
    nativeCompletedWeakRows.getD 5 0 = inSourceXi5Pre := by
  simp [nativeCompletedWeakRows, inSourceXi5Pre]

/-- IN-SOURCE-ROWS on the actual completed OLD law. The four observables are
the ENNReal expectation rows at cutoff `m`, all in the single true frame
`Annealed.sigmaBar M m`; `r=0` is the actual ordinary-mean prefix input. -/
theorem in_source_rows_source
    (M : ABKModel 2) (m : ℤ)
    (hSmall : NativeSourceSmallerGammaBounds M m) :
    ordinaryMean M m ≤ ENNReal.ofReal (theta M * (3 / 50 : ℝ)) ∧
      nativeCompletedSourceMean M m 4 ≤
        ENNReal.ofReal (theta M * (inSourceA4 : ℝ)) ∧
      nativeCompletedSourceMean M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceA5 : ℝ)) ∧
      nativeCompletedSourceWeak M m 5 ≤
        ENNReal.ofReal (theta M * (inSourceXi5Pre : ℝ)) ∧
      nativeCompletedSourceMean M m 0 = ordinaryMean M m := by
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hmean0 := hSmall.mean (0 : Fin 6)
  have hmean0' : nativeCompletedSourceMean M m 0 ≤
      ENNReal.ofReal (theta M * (3 / 50 : ℝ)) := by
    change nativeCompletedSourceMean M m 0 ≤
      ENNReal.ofReal (theta M * ((nativeCompletedMeanRows.getD 0 0 : ℚ) : ℝ)) at hmean0
    rw [nativeCompletedMeanRow_zero] at hmean0
    convert hmean0 using 1 <;> norm_num
  have hordinary : ordinaryMean M m ≤
      ENNReal.ofReal (theta M * (3 / 50 : ℝ)) := by
    rw [← native_completed_source_mean_zero M m]
    exact hmean0'
  have hmean4 := hSmall.mean (⟨4, by omega⟩ : Fin 6)
  have hmean4' : nativeCompletedSourceMean M m 4 ≤
      ENNReal.ofReal (theta M * (inSourceA4 : ℝ)) := by
    change nativeCompletedSourceMean M m 4 ≤
      ENNReal.ofReal (theta M * ((nativeCompletedMeanRows.getD 4 0 : ℚ) : ℝ)) at hmean4
    apply hmean4.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast nativeCompletedMeanRow_four_le) htheta
  have hmean5 := hSmall.mean (⟨5, by omega⟩ : Fin 6)
  have hmean5' : nativeCompletedSourceMean M m 5 ≤
      ENNReal.ofReal (theta M * (inSourceA5 : ℝ)) := by
    change nativeCompletedSourceMean M m 5 ≤
      ENNReal.ofReal (theta M * ((nativeCompletedMeanRows.getD 5 0 : ℚ) : ℝ)) at hmean5
    apply hmean5.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast nativeCompletedMeanRow_five_le) htheta
  have hweak5 := hSmall.weak (⟨5, by omega⟩ : Fin 6)
  have hweak5' : nativeCompletedSourceWeak M m 5 ≤
      ENNReal.ofReal (theta M * (inSourceXi5Pre : ℝ)) := by
    change nativeCompletedSourceWeak M m 5 ≤
      ENNReal.ofReal (theta M * ((nativeCompletedWeakRows.getD 5 0 : ℚ) : ℝ)) at hweak5
    simpa only [nativeCompletedWeakRow_five_eq] using hweak5
  exact ⟨hordinary, hmean4', hmean5', hweak5',
    native_completed_source_mean_zero M m⟩

end ASDExplicitGamma.Inverse
