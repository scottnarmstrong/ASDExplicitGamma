module
public import ASDExplicitGamma.Numerics.Native.PanelFormula
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum

/-! Rigorous right-endpoint integration over all 512 native panel interiors. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

private theorem native_nonneg_interval_integrable (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ici 0)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  apply MonotoneOn.intervalIntegrable
  apply hf.mono
  rw [Set.uIcc_of_le hab]
  intro x hx
  exact ha.trans hx.1

private theorem native_integral_right (f : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Ici 0)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, f x) ≤ (b-a)*f b := by
  have hint := native_nonneg_interval_integrable f hf a b ha hab
  have hm := intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
    (fun x hx => hf (ha.trans hx.1) (ha.trans hab) hx.2)
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using hm

/-- Every panel interior is dominated by its right endpoint, with no grid-only monotonicity assumption. -/
theorem native_integral_le_512_sum (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Ici 0)) :
    (∫ x in (0 : ℝ)..1, f x) ≤
      (∑ j ∈ Finset.range 512, f ((j+1 : ℕ)/512))/512 := by
  have ha (j : ℕ) : (0 : ℝ) ≤ (j : ℝ)/512 :=
    div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hab (j : ℕ) : (j : ℝ)/512 ≤ ((j+1 : ℕ) : ℝ)/512 :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (by norm_num)
  have hi (j : ℕ) : IntervalIntegrable f MeasureTheory.volume
      ((j : ℝ)/512) ((j+1 : ℕ)/512) := by
    apply native_nonneg_interval_integrable f hf _ _ (by positivity)
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (by norm_num)
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ)/512) (n := 512) (fun j _ => hi j)
  have he : (∫ x in (0 : ℝ)..1, f x) =
      ∑ j ∈ Finset.range 512, ∫ x in ((j : ℝ)/512)..((j+1 : ℕ)/512), f x := by
    simpa only [Nat.cast_zero,zero_div,Nat.cast_ofNat,div_self (by norm_num : (512 : ℝ) ≠ 0)] using hs.symm
  rw [he,Finset.sum_div]
  apply Finset.sum_le_sum
  intro j hj
  have h := native_integral_right f hf ((j : ℝ)/512) ((j+1 : ℕ)/512)
    (ha j) (hab j)
  have hw : ((j+1 : ℕ) : ℝ)/512-(j : ℝ)/512 = 1/512 := by push_cast; ring
  rw [hw] at h
  simpa only [div_eq_mul_inv,one_mul,mul_comm] using h

end ASDExplicitGamma.Numerics.Native
