module
public import ASDExplicitGamma.Numerics.Native.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A 60-decimal log-3 enclosure for the boundary-fixed native panel replay.
The interval follows from the elementary positive log-atanh partial sum and its full tail.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

def nativeLogSeries (q : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, q^(2*i+1)/(2*i+1 : ℕ)

theorem nativeLogSeries_cast (q : ℚ) (n : ℕ) :
    (nativeLogSeries q n : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ)^(2*i+1)/(2*i+1 : ℕ) := by
  simp only [nativeLogSeries, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

def nativeLogThreeLower : ℚ := 1098612288668109691395245236922525704647490557822749451734694/10^60
def nativeLogThreeUpper : ℚ := 1098612288668109691395245236922525704647490557822749451734695/10^60

theorem nativeLogThree_rational_checks :
    nativeLogThreeLower ≤ 2*nativeLogSeries (1/2) 110 ∧
    2*(nativeLogSeries (1/2) 110+(1/2 : ℚ)^221/(1-(1/2 : ℚ)^2)) ≤ nativeLogThreeUpper := by
  decide +kernel

theorem nativeLogThree_series_bound (n : ℕ) :
    2*(nativeLogSeries (1/2) n : ℝ) ≤ Real.log 3 ∧
    Real.log 3 ≤ 2*((nativeLogSeries (1/2) n : ℝ)+(1/2 : ℝ)^(2*n+1)/(1-(1/2 : ℝ)^2)) := by
  have hlo := Real.sum_range_le_log_div (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) n
  have hhi := Real.log_div_le_sum_range_add (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1) n
  have hr : ((1+(1/2 : ℝ))/(1-1/2)) = 3 := by norm_num
  rw [hr] at hlo hhi
  have hc := nativeLogSeries_cast (1/2) n
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hc
  rw [← hc] at hlo hhi
  constructor <;> linarith only [hlo,hhi]

theorem nativeLogThree_real :
    (nativeLogThreeLower : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ (nativeLogThreeUpper : ℝ) := by
  have h := nativeLogThree_series_bound 110
  have hlo : (nativeLogThreeLower : ℝ) ≤ 2*(nativeLogSeries (1/2) 110 : ℝ) := by
    have hn := (Rat.cast_le (K := ℝ)).2 nativeLogThree_rational_checks.1
    norm_num only [Rat.cast_mul, Rat.cast_ofNat] at hn
    exact hn
  have hhi := (Rat.cast_le (K := ℝ)).2 nativeLogThree_rational_checks.2
  norm_num only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat] at hhi
  constructor
  · exact hlo.trans h.1
  · apply h.2.trans
    convert hhi using 1; norm_num

def nativeLogThreeInterval : QInterval :=
  ⟨nativeLogThreeLower,nativeLogThreeUpper,by decide +kernel⟩

theorem nativeLogThreeInterval_sound : QInterval.Contains nativeLogThreeInterval (Real.log 3) :=
  nativeLogThree_real

end ASDExplicitGamma.Numerics.Native
