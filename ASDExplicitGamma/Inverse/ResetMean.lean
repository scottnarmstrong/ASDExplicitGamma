module

public import ASDExplicitGamma.Inverse.ResetChronology
public import ASDExplicitGamma.Variational.TrueFrame

/-! The separate buffer mean supplies 29/25 in the true completed frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3

/-- The ordinary real expectation is the real value of the frozen buffer mean. -/
theorem bufferMean_integral (M : ABKModel 2) (n : ℤ) :
    (∫ a : RegCoeffField 2,
      traceDefect (cubeSet (originCube 2 (n-40))) a.toFun (Annealed.sigmaBar M n : ℝ)
      ∂(Cutoff.coefficientCutoffLaw M n)) = (bufferMean M n).toReal := by
  have hi := Variational.integrable_traceDefect_cutoffLaw M n (originCube 2 (n-40))
    (Annealed.sigmaBar M n : ℝ)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable hi.aestronglyMeasurable]
  change (∫ ω, cutoffTraceDefect M n (n-40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (Variational.cutoffTraceDefect_nonneg M n (n-40)))
    (Variational.cutoffTraceDefect_measurable M n (n-40)).aestronglyMeasurable

/-- The buffer coordinate and gamma domain give the unclipped full-matrix mean cap.
Any positive clipping is subsequently bounded by this same matrix in Loewner order. -/
theorem reset_full_matrix_mean (M : ABKModel 2) (n : ℤ) (hg : 0 < M.gamma)
    (hgmax : M.gamma ≤ gammaZero)
    (hbuf : bufferMean M n ≤ ENNReal.ofReal (8/25*theta M)) :
    ∃ alpha beta : ℝ, 1 ≤ alpha ∧ 1 ≤ beta ∧ alpha ≤ 29/25 ∧ beta ≤ 29/25 ∧
      ∀ z : Vec 2,
        Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
          (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M n)
            (translateSet z (cubeSet (originCube 2 (n-40))))) =
          Book.Ch02.blockDiag (alpha • (1 : Mat 2)) (beta • (1 : Mat 2)) ∧
        BlockMatLoewnerLE
          (Variational.frameMatrix (Annealed.sigmaBar M n : ℝ)
            (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M n)
              (translateSet z (cubeSet (originCube 2 (n-40))))))
          (Book.Ch02.blockDiag ((29/25 : ℝ) • (1 : Mat 2)) ((29/25 : ℝ) • (1 : Mat 2))) := by
  have hg0 : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  have ht0 : 0 ≤ theta M := (div_pos hg hg0).le
  have ht1 : theta M ≤ 1 := (div_le_one hg0).mpr hgmax
  have hc : (8/25 : ℝ)*theta M ≤ 8/25 := by linarith only [ht1]
  have hb : (bufferMean M n).toReal ≤ 8/25 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbuf
    rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) ht0)] at h
    exact h.trans hc
  have htrace : (∫ a : RegCoeffField 2,
      traceDefect (translateSet (0 : Vec 2) (cubeSet (originCube 2 (n-40)))) a.toFun
        (Annealed.sigmaBar M n : ℝ) ∂(Cutoff.coefficientCutoffLaw M n)) ≤ (8/25 : ℝ) := by
    simpa only [translateSet_zero,bufferMean_integral] using hb
  have h := Variational.exists_trueFrame_mean_bounds M n (n-40) 0 htrace
  norm_num only [show (1+(8/25)/2 : ℝ) = 29/25 by norm_num] at h
  exact h

end ASDExplicitGamma.Inverse
