module

public import ASDExplicitGamma.Triadic.HistoryMonotone
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Extended-valued histories: the even/odd proof also applies before proving finiteness. -/
@[expose] public section
namespace ASDExplicitGamma.Triadic
open scoped ENNReal

/-- No summability premise is needed for a series of nonnegative extended terms. -/
theorem geometric_history_square_le_ennreal (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (d : ℕ → ℝ≥0∞) (hm : Monotone d) :
    ENNReal.ofReal (1-q^2)*(∑' j : ℕ, ENNReal.ofReal ((q^2)^j)*d j) ≤
      ENNReal.ofReal (1-q)*(∑' j : ℕ, ENNReal.ofReal (q^j)*d j) := by
  let S := ∑' j : ℕ, ENNReal.ofReal ((q^2)^j)*d j
  have hE : S ≤ ∑' j : ℕ, ENNReal.ofReal (q^(2*j))*d (2*j) := by
    apply ENNReal.tsum_le_tsum
    intro j
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left (hm (by omega : j ≤ 2*j)) (zero_le : (0:ℝ≥0∞) ≤ _)
  have hO : ENNReal.ofReal q*S ≤ ∑' j : ℕ, ENNReal.ofReal (q^(2*j+1))*d (2*j+1) := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro j
    rw [pow_succ q (2*j),pow_mul q 2 j,ENNReal.ofReal_mul (pow_nonneg (sq_nonneg q) j)]
    have hh := mul_le_mul_of_nonneg_left (hm (by omega : j ≤ 2*j+1))
      (zero_le : (0:ℝ≥0∞) ≤ ENNReal.ofReal q*ENNReal.ofReal ((q^2)^j))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hEO := tsum_even_add_odd (f := fun j : ℕ => ENNReal.ofReal (q^j)*d j)
    ENNReal.summable ENNReal.summable
  have ht : ENNReal.ofReal (1+q)*S ≤ ∑' j : ℕ, ENNReal.ofReal (q^j)*d j := by
    rw [ENNReal.ofReal_add (by norm_num) hq.le,ENNReal.ofReal_one,add_mul,one_mul]
    exact hEO ▸ add_le_add hE hO
  have hh := mul_le_mul_of_nonneg_left ht (zero_le : (0:ℝ≥0∞) ≤ ENNReal.ofReal (1-q))
  have he : ENNReal.ofReal (1-q)*ENNReal.ofReal (1+q) = ENNReal.ofReal (1-q^2) := by
    rw [← ENNReal.ofReal_mul (by linarith only [hq1])]
    congr 1
    ring
  simpa only [← mul_assoc,he,S] using hh

/-- The raw doubled-discount history in terms of the normalized original history. -/
theorem geometric_history_raw_le_ennreal (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (d : ℕ → ℝ≥0∞) (hm : Monotone d) :
    (∑' j : ℕ, ENNReal.ofReal ((q^2)^j)*d j) ≤
      ENNReal.ofReal ((1-q^2)⁻¹)*
        (ENNReal.ofReal (1-q)*∑' j : ℕ, ENNReal.ofReal (q^j)*d j) := by
  have hp : 0 < 1-q^2 := by nlinarith only [hq,hq1]
  have h := mul_le_mul_of_nonneg_left (geometric_history_square_le_ennreal q hq hq1 d hm)
    (zero_le : (0:ℝ≥0∞) ≤ ENNReal.ofReal ((1-q^2)⁻¹))
  have he : ENNReal.ofReal ((1-q^2)⁻¹)*ENNReal.ofReal (1-q^2) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hp.le),inv_mul_cancel₀ hp.ne',ENNReal.ofReal_one]
  simpa only [← mul_assoc,he,one_mul] using h

end ASDExplicitGamma.Triadic
