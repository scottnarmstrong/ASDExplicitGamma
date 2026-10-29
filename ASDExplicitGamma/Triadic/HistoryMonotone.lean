module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Normalized geometric histories of nonnegative nondecreasing sequences.
Summability is explicit: no divergent real tsum is interpreted as an extended sum. -/
@[expose] public section
namespace ASDExplicitGamma.Triadic

noncomputable def geometricHistory (q : ℝ) (d : ℕ → ℝ) : ℝ :=
  (1-q)*∑' j : ℕ, q^j*d j

/-- Grouping the full history into even/odd depths proves stochastic monotonicity. -/
theorem geometric_history_square_le (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j) (hm : Monotone d)
    (hs : Summable (fun j : ℕ => q^j*d j)) :
    Summable (fun j : ℕ => (q^2)^j*d j) ∧
      geometricHistory (q^2) d ≤ geometricHistory q d := by
  have hqq : q^2 ≤ q := by nlinarith only [hq,hq1]
  have hsq : Summable (fun j : ℕ => (q^2)^j*d j) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg (sq_nonneg q) j) (hd j))
      (fun j => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg q) hqq j) (hd j)) hs
  have he : Summable (fun j : ℕ => q^(2*j)*d (2*j)) :=
    hs.comp_injective (show Function.Injective (fun j : ℕ => 2*j) from by
      intro i j h
      change 2*i = 2*j at h
      omega)
  have ho : Summable (fun j : ℕ => q^(2*j+1)*d (2*j+1)) :=
    hs.comp_injective (show Function.Injective (fun j : ℕ => 2*j+1) from by
      intro i j h
      change 2*i+1 = 2*j+1 at h
      omega)
  have hE : (∑' j : ℕ, (q^2)^j*d j) ≤ ∑' j : ℕ, q^(2*j)*d (2*j) := by
    apply Summable.tsum_le_tsum _ hsq he
    intro j
    rw [pow_mul]
    exact mul_le_mul_of_nonneg_left (hm (by omega : j ≤ 2*j)) (pow_nonneg (sq_nonneg q) j)
  have hO : q*(∑' j : ℕ, (q^2)^j*d j) ≤ ∑' j : ℕ, q^(2*j+1)*d (2*j+1) := by
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum _ (hsq.mul_left q) ho
    intro j
    rw [pow_succ q (2*j),pow_mul q 2 j]
    have hh := mul_le_mul_of_nonneg_left (hm (by omega : j ≤ 2*j+1))
      (mul_nonneg hq.le (pow_nonneg (sq_nonneg q) j))
    convert hh using 1 <;> ring
  have hEO := tsum_even_add_odd (f := fun j : ℕ => q^j*d j) he ho
  have ht : (1+q)*(∑' j : ℕ, (q^2)^j*d j) ≤ ∑' j : ℕ, q^j*d j := by
    linarith only [hE,hO,hEO]
  refine ⟨hsq,?_⟩
  have hh := mul_le_mul_of_nonneg_left ht (by linarith only [hq1] : 0 ≤ 1-q)
  unfold geometricHistory
  convert hh using 1; ring

/-- The normalized and raw history consequences, with their positive normalization. -/
theorem geometric_history_raw_le (q : ℝ) (hq : 0 < q) (hq1 : q < 1)
    (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j) (hm : Monotone d)
    (hs : Summable (fun j : ℕ => q^j*d j)) :
    (∑' j : ℕ, (q^2)^j*d j) ≤ (1-q^2)⁻¹*geometricHistory q d ∧
      geometricHistory (q^2) d ≤ geometricHistory q d := by
  have hb := (geometric_history_square_le q hq hq1 d hd hm hs).2
  have hp : 0 < 1-q^2 := by nlinarith only [hq,hq1]
  refine ⟨?_,hb⟩
  rw [inv_mul_eq_div,le_div_iff₀ hp]
  simpa only [geometricHistory,mul_comm] using hb

/-- Integer powers of the geometric ratio are exactly the source real-power weights. -/
theorem history_rpow_weight (t : ℝ) (j : ℕ) :
    ((3 : ℝ)^t)^j = (3 : ℝ)^(t*j) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]

/-- TR-HISTORY-MONOTONE in the source normalization, with honest summability. -/
theorem history_monotone_source (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j) (hm : Monotone d)
    (hs : Summable (fun j : ℕ => (3 : ℝ)^(-(1/4 : ℝ)*j)*d j)) :
    (∑' j : ℕ, (3 : ℝ)^(-(1/2 : ℝ)*j)*d j) ≤
      (1-(3 : ℝ)^(-(1/2 : ℝ)))⁻¹*
        ((1-(3 : ℝ)^(-(1/4 : ℝ)))*∑' j : ℕ, (3 : ℝ)^(-(1/4 : ℝ)*j)*d j) ∧
    (1-(3 : ℝ)^(-(1/2 : ℝ)))*(∑' j : ℕ, (3 : ℝ)^(-(1/2 : ℝ)*j)*d j) ≤
      (1-(3 : ℝ)^(-(1/4 : ℝ)))*∑' j : ℕ, (3 : ℝ)^(-(1/4 : ℝ)*j)*d j := by
  have hq : (0 : ℝ) < (3 : ℝ)^(-(1/4 : ℝ)) := by positivity
  have hq1 : (3 : ℝ)^(-(1/4 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hq2 : ((3 : ℝ)^(-(1/4 : ℝ)))^2 = (3 : ℝ)^(-(1/2 : ℝ)) := by
    rw [history_rpow_weight]
    norm_num
  have hs' : Summable (fun j : ℕ => ((3 : ℝ)^(-(1/4 : ℝ)))^j*d j) := by
    simpa only [history_rpow_weight] using hs
  have hb := geometric_history_raw_le _ hq hq1 d hd hm hs'
  simpa only [geometricHistory,hq2,history_rpow_weight] using hb

end ASDExplicitGamma.Triadic
