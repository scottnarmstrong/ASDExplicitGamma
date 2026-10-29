module

public import ASDExplicitGamma.Triadic.DiagLattice
public import Mathlib.Data.Fin.Basic

/-! Exact odd-reflection counting on the doubled source period. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- Reflect the second half of the doubled cell period back to the parent. -/
def diagReflectIndex (N : ℕ) (k : Fin (2 * N)) : Fin N :=
  ⟨if k.val < N then k.val else 2 * N - 1 - k.val, by
    have hk := k.isLt
    split_ifs <;> omega⟩

/-- The source odd sign on the two halves of the doubled period. -/
def diagReflectSign (N : ℕ) (k : Fin (2 * N)) : ℝ := if k.val < N then 1 else -1

def diagReflectEven (N : ℕ) (f : Fin N → ℝ) (k : Fin (2 * N)) : ℝ :=
  f (diagReflectIndex N k)

def diagReflectOdd (N : ℕ) (f : Fin N → ℝ) (k : Fin (2 * N)) : ℝ :=
  diagReflectSign N k * f (diagReflectIndex N k)

/-- Actual cyclic shift on the doubled grid, including the last-to-first edge. -/
def diagPeriodShift (N : ℕ) : Equiv.Perm (Fin (2 * N)) where
  toFun k := ⟨if k.val + 1 < 2 * N then k.val + 1 else 0, by
    have hk := k.isLt
    split_ifs <;> omega⟩
  invFun k := ⟨if k.val = 0 then 2 * N - 1 else k.val - 1, by
    have hk := k.isLt
    split_ifs <;> omega⟩
  left_inv k := by
    apply Fin.ext
    dsimp
    have hk := k.isLt
    by_cases hn : k.val + 1 < 2 * N
    · have hne : k.val + 1 ≠ 0 := by omega
      simp only [ite_eq_left hn, ite_eq_right hne]
      omega
    · have hlast : k.val = 2 * N - 1 := by omega
      simp only [ite_eq_right hn]
      exact hlast.symm
  right_inv k := by
    apply Fin.ext
    dsimp
    have hk := k.isLt
    split_ifs <;> omega

@[simp] theorem diagPeriodShift_val (N : ℕ) (k : Fin (2 * N)) :
    (diagPeriodShift N k).val = if k.val + 1 < 2 * N then k.val + 1 else 0 := rfl

/-- Enumeration of reflected cells by two copies of the original grid. -/
def diagReflectionEquiv (N : ℕ) : (Fin N ⊕ Fin N) ≃ Fin (2 * N) where
  toFun k := match k with
    | Sum.inl k => ⟨k.val, by have := k.isLt; omega⟩
    | Sum.inr k => ⟨2 * N - 1 - k.val, by have := k.isLt; omega⟩
  invFun k := if hk : k.val < N then Sum.inl ⟨k.val, hk⟩
    else Sum.inr ⟨2 * N - 1 - k.val, by have := k.isLt; omega⟩
  left_inv k := by
    cases k with
    | inl k =>
        simp only [dite_eq_left k.isLt]
    | inr k =>
        have hk := k.isLt
        have hn : ¬2 * N - 1 - k.val < N := by omega
        simp only [dite_eq_right hn]
        congr 1
        apply Fin.ext
        dsimp
        omega
  right_inv k := by
    have hk := k.isLt
    dsimp
    split_ifs
    · rfl
    · apply Fin.ext
      dsimp
      omega

theorem diagReflectIndex_inl (N : ℕ) (k : Fin N) :
    diagReflectIndex N (diagReflectionEquiv N (Sum.inl k)) = k := by
  apply Fin.ext
  change (if k.val < N then k.val else 2 * N - 1 - k.val) = k.val
  exact ite_eq_left k.isLt

theorem diagReflectIndex_inr (N : ℕ) (k : Fin N) :
    diagReflectIndex N (diagReflectionEquiv N (Sum.inr k)) = k := by
  have hk := k.isLt
  have hn : ¬2 * N - 1 - k.val < N := by omega
  apply Fin.ext
  change (if 2 * N - 1 - k.val < N then 2 * N - 1 - k.val else
    2 * N - 1 - (2 * N - 1 - k.val)) = k.val
  rw [ite_eq_right hn]
  omega

/-- Both reflected copies carry exactly the same normalized squared budget. -/
theorem diagReflectEven_sum (N : ℕ) (f : Fin N → ℝ) :
    (∑ k : Fin (2 * N), diagReflectEven N f k) = 2 * ∑ k : Fin N, f k := by
  rw [← Equiv.sum_comp (diagReflectionEquiv N) (diagReflectEven N f), Fintype.sum_sum_type]
  simp only [diagReflectEven, diagReflectIndex_inl, diagReflectIndex_inr]
  ring

theorem diagReflectSign_sq (N : ℕ) (k : Fin (2 * N)) : diagReflectSign N k ^ 2 = 1 := by
  unfold diagReflectSign
  split_ifs <;> norm_num

theorem diagReflectOdd_sum_sq (N : ℕ) (f : Fin N → ℝ) :
    (∑ k : Fin (2 * N), diagReflectOdd N f k ^ 2) = 2 * ∑ k : Fin N, f k ^ 2 := by
  have h (k : Fin (2 * N)) : diagReflectOdd N f k ^ 2 =
      diagReflectEven N (fun i => f i ^ 2) k := by
    rw [diagReflectOdd, mul_pow, diagReflectSign_sq, one_mul]
    rfl
  simp only [h]
  exact diagReflectEven_sum N (fun i => f i ^ 2)

theorem diagReflectEven_sum_sq (N : ℕ) (f : Fin N → ℝ) :
    (∑ k : Fin (2 * N), diagReflectEven N f k ^ 2) = 2 * ∑ k : Fin N, f k ^ 2 :=
  diagReflectEven_sum N (fun i => f i ^ 2)

end

end ASDExplicitGamma.Triadic
