module

public import ASDExplicitGamma.Cold.NativeTrace
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # The genuine native strong input supplies the complete fine-tail norm sum -/

@[expose] public section
noncomputable section
open MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The source beta power at a natural depth is exactly the frozen strong20 weight. -/
theorem cold_native_beta_power (r : ℕ) :
    coldHistoryBeta^r = (3:ℝ)^(-(3/20:ℝ)*(r:ℝ)) := by
  unfold coldHistoryBeta
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]

/-- The literal weighted ENNReal terms of the genuine native strong input. -/
def coldNativeStrongTerm (M : ABKModel 2) (m : ℤ) (r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1-coldHistoryAlpha)*ENNReal.ofReal (coldHistoryBeta^r)*
    eLpNorm (cutoffTraceDefect M m (m-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure

/-- Exact equality with the frozen infinite strong20 definition. -/
theorem tsum_coldNativeStrongTerm (M : ABKModel 2) (m : ℤ) :
    (∑' r, coldNativeStrongTerm M m r) = strong20 M m := by
  unfold coldNativeStrongTerm strong20
  simp_rw [cold_native_beta_power,mul_assoc]
  rw [ENNReal.tsum_mul_left]
  rfl

/-- Every negative-lag trace has actual finite twentieth moment from the genuine strong input. -/
theorem cold_native_fine_memLp {M : ABKModel 2} {m : ℤ} {S : ℝ}
    (hstrong : strong20 M m ≤ ENNReal.ofReal S) (r : ℕ) :
    MemLp (cutoffTraceDefect M m (m-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hterm : coldNativeStrongTerm M m r ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((ENNReal.le_tsum r).trans (by rw [tsum_coldNativeStrongTerm]; exact hstrong))
  have hweight : ENNReal.ofReal (1-coldHistoryAlpha)*ENNReal.ofReal (coldHistoryBeta^r) ≠ 0 := by
    apply mul_ne_zero
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr coldHistoryAlpha_lt_one))
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos coldHistoryBeta_pos r))
  apply lt_top_iff_ne_top.mpr
  intro htop
  apply hterm
  unfold coldNativeStrongTerm
  rw [htop,ENNReal.mul_top hweight]

/-- The exact real weighted fine-history terms, with genuine L20 norms. -/
def coldNativeStrongRealTerm (M : ABKModel 2) (m : ℤ) (r : ℕ) : ℝ :=
  (1-coldHistoryAlpha)*coldHistoryBeta^r*
    lpNorm (cutoffTraceDefect M m (m-r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure

/-- Each real norm term is the exact toReal of its frozen extended-valued term. -/
theorem coldNativeStrongRealTerm_eq_toReal (M : ABKModel 2) (m : ℤ) (r : ℕ) :
    coldNativeStrongRealTerm M m r = (coldNativeStrongTerm M m r).toReal := by
  simp only [coldNativeStrongRealTerm,coldNativeStrongTerm,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr coldHistoryAlpha_le_one),
    ENNReal.toReal_ofReal (pow_nonneg coldHistoryBeta_pos.le r),lpNorm]

/-- The genuine strong20 cap supplies the complete real fine-tail sum and its summability.
No finite truncation or replacement by a geometric root-only cap is used. -/
theorem cold_native_strong_sum {M : ABKModel 2} {m : ℤ} {S : ℝ} (hS : 0 ≤ S)
    (hstrong : strong20 M m ≤ ENNReal.ofReal S) :
    Summable (coldNativeStrongRealTerm M m) ∧ (∑' r, coldNativeStrongRealTerm M m r) ≤ S := by
  have ht : (∑' r, coldNativeStrongTerm M m r) ≠ ∞ := by
    rw [tsum_coldNativeStrongTerm]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hstrong
  have he : coldNativeStrongRealTerm M m = (fun r => (coldNativeStrongTerm M m r).toReal) :=
    funext (coldNativeStrongRealTerm_eq_toReal M m)
  rw [he]
  refine ⟨ENNReal.summable_toReal ht,?_⟩
  rw [← ENNReal.tsum_toReal_eq (fun r => ENNReal.ne_top_of_tsum_ne_top ht r),tsum_coldNativeStrongTerm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hstrong).trans_eq (ENNReal.toReal_ofReal hS)

end ASDExplicitGamma.Cold
