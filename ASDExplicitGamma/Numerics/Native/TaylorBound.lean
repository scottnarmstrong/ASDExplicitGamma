module
public import ASDExplicitGamma.Numerics.Native.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Entrywise positive matrix Taylor control for the 153 native systems. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

noncomputable section
local instance nativeTaylorMatrixRing (n : ℕ) : NormedRing (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedRing
local instance nativeTaylorMatrixAlgebra (n : ℕ) : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedAlgebra

/-- Row-sum control propagates through all powers of the nonnegative matrix. -/
theorem native_matrix_power_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (hrow : ∀ i, ∑ j, G i j ≤ 6)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (k : ℕ) :
    ∀ i, 0 ≤ (G^k *ᵥ v) i ∧ (G^k *ᵥ v) i ≤ 6^k := by
  induction k with
  | zero => simpa only [pow_zero, Matrix.one_mulVec, pow_zero] using hv
  | succ k ih =>
    intro i
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    constructor
    · rw [Matrix.mulVec_apply_eq_sum]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hG i j) (ih j).1)
    · calc
        (G *ᵥ (G^k *ᵥ v)) i ≤ ∑ j, G i j*6^k :=
          by
            rw [Matrix.mulVec_apply_eq_sum]
            exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j).2 (hG i j))
        _ = (∑ j, G i j)*6^k := (Finset.sum_mul ..).symm
        _ ≤ 6*6^k := mul_le_mul_of_nonneg_right (hrow i) (by positivity)
        _ = 6^(k+1) := by rw [pow_succ]; ring

/-- Multiplying the actual matrix exponential by a vector is the complete Taylor action. -/
theorem native_matrix_exp_hasSum {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (i : Fin n) :
    HasSum (fun k : ℕ => ((G^k *ᵥ v) i)/(Nat.factorial k : ℝ))
      ((NormedSpace.exp G *ᵥ v) i) := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) G
  have hh (j : Fin n) := ((Pi.hasSum.mp (Pi.hasSum.mp hs i)) j).mul_right (v j)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hh j)
  convert hsum using 1
  · funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
      div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rfl

def nativeScalarTaylorTerm (k : ℕ) : ℝ := 6^k/(Nat.factorial k : ℝ)

theorem nativeScalarTaylorTerm_succ (k : ℕ) :
    nativeScalarTaylorTerm (k+1) = nativeScalarTaylorTerm k*(6/(k+1 : ℕ)) := by
  simp only [nativeScalarTaylorTerm, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  push_cast
  field_simp

/-- Every term beyond degree 160 is paid by the complete ratio-6/162 tail. -/
theorem native_scalar_tail_ratio (k : ℕ) :
    nativeScalarTaylorTerm (161+k) ≤ nativeScalarTaylorTerm 161*(6/162 : ℝ)^k := by
  induction k with
  | zero => simp only [Nat.add_zero, pow_zero, mul_one, le_refl]
  | succ k ih =>
    rw [Nat.add_succ, nativeScalarTaylorTerm_succ]
    have hdN : (162 : ℕ) ≤ 161+k+1 := by omega
    have hd : (162 : ℝ) ≤ (161+k+1 : ℕ) := by exact_mod_cast hdN
    have hratio : (6 : ℝ)/(161+k+1 : ℕ) ≤ 6/162 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hd
    calc
      nativeScalarTaylorTerm (161+k)*(6/(161+k+1 : ℕ)) ≤
          (nativeScalarTaylorTerm 161*(6/162 : ℝ)^k)*(6/162) :=
        mul_le_mul ih hratio (by positivity) (by unfold nativeScalarTaylorTerm; positivity)
      _ = nativeScalarTaylorTerm 161*(6/162 : ℝ)^(k+1) := by rw [pow_succ]; ring

/-- The actual matrix exponential is dominated entrywise by the positive degree-160 polynomial
and the source's complete common scalar remainder. -/
theorem native_matrix_exp_taylor_bound {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (hrow : ∀ i, ∑ j, G i j ≤ 6)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (i : Fin n) :
    (NormedSpace.exp G *ᵥ v) i ≤
      (∑ k ∈ Finset.range 161, ((G^k *ᵥ v) i)/(Nat.factorial k : ℝ))+
      (6^161/(Nat.factorial 161 : ℝ))/(1-6/162) := by
  let a : ℕ → ℝ := fun k => ((G^k *ᵥ v) i)/(Nat.factorial k : ℝ)
  have ha := native_matrix_exp_hasSum G v i
  have hnonneg (k : ℕ) : 0 ≤ a k := by
    exact div_nonneg (native_matrix_power_bound G v hG hrow hv k i).1 (Nat.cast_nonneg _)
  have hterm (k : ℕ) : a k ≤ nativeScalarTaylorTerm k :=
    div_le_div_of_nonneg_right (native_matrix_power_bound G v hG hrow hv k i).2
      (Nat.cast_nonneg _)
  have hmajor (k : ℕ) : a (k+161) ≤ nativeScalarTaylorTerm 161*(6/162 : ℝ)^k := by
    exact (hterm _).trans (by simpa only [Nat.add_comm] using native_scalar_tail_ratio k)
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(6/162 : ℝ)‖ < 1)).mul_left
    (nativeScalarTaylorTerm 161)
  have htail := hg.summable.of_nonneg_of_le (fun k => hnonneg _) hmajor
  have htailBound := htail.tsum_le_tsum hmajor hg.summable
  rw [hg.tsum_eq] at htailBound
  have hsplit := ha.summable.sum_add_tsum_nat_add 161
  rw [ha.tsum_eq] at hsplit
  rw [← hsplit]
  apply add_le_add le_rfl
  simpa only [a, nativeScalarTaylorTerm, div_eq_mul_inv] using htailBound

end
end ASDExplicitGamma.Numerics.Native
