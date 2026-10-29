module

public import ASDExplicitGamma.Triadic.HilbertPoincareNorms
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Exact general-weight positive Haar product bound for Hilbert and operator fields. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

theorem sqrt_tsum_sq_add_le (a b : ℕ → ℝ)
    (ha : Summable (fun n => a n ^ 2)) (hb : Summable (fun n => b n ^ 2)) :
    Real.sqrt (∑' n, (a n + b n) ^ 2) ≤
      Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, b n ^ 2) := by
  have hmem (c : ℕ → ℝ) (hc : Summable (fun n => c n ^ 2)) : Memℓp c (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using hc
  let A : lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) := ⟨a, hmem a ha⟩
  let B : lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) := ⟨b, hmem b hb⟩
  have hA : ‖A‖ ^ 2 = ∑' n, a n ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) A
    simpa [A, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
  have hB : ‖B‖ ^ 2 = ∑' n, b n ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) B
    simpa [B, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
  have hAB : ‖A + B‖ ^ 2 = ∑' n, (a n + b n) ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (A + B)
    have h' : ‖A + B‖ ^ 2 = ∑' n, ‖(A + B) n‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
    calc
      ‖A + B‖ ^ 2 = ∑' n, ‖(A + B) n‖ ^ 2 := h'
      _ = ∑' n, (a n + b n) ^ 2 := by
        apply tsum_congr
        intro n
        rw [lp.coeFn_add]
        change ‖(a n + b n)‖ ^ 2 = (a n + b n) ^ 2
        simp [Real.norm_eq_abs, sq_abs]
  have hnorm := norm_add_le A B
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBn : 0 ≤ ‖B‖ := norm_nonneg _
  have hABn : 0 ≤ ‖A + B‖ := norm_nonneg _
  calc
    Real.sqrt (∑' n, (a n + b n) ^ 2) = ‖A + B‖ := by
      rw [← hAB, Real.sqrt_sq_eq_abs, abs_of_nonneg hABn]
    _ ≤ ‖A‖ + ‖B‖ := hnorm
    _ = Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, b n ^ 2) := by
      rw [← hA, ← hB, Real.sqrt_sq_eq_abs, abs_of_nonneg hAn,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hBn]


end
end ASDExplicitGamma.Triadic
