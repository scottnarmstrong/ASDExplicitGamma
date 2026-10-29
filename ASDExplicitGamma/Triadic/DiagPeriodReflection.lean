module

public import ASDExplicitGamma.Triadic.DiagPeriodGrid

/-! Exact face reflections on the doubled finite source grid. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators Fin.CommRing

noncomputable section

theorem diagPeriodReflection_val {N : ℕ} (hN : 0 < N) [NeZero (2*N)] (k : Fin (2*N)) :
    (-k-1).val = 2*N-1-k.val := by
  have he : -k-1 = -(k+1) := by abel
  rw [he, ← diagPeriodShift_eq_add_one hN, Fin.val_neg', diagPeriodShift_val]
  have hk := k.isLt
  split_ifs with h
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [Nat.sub_zero, Nat.mod_self]
    omega

theorem diagReflectIndex_reflection {N : ℕ} (hN : 0 < N) [NeZero (2*N)] (k : Fin (2*N)) :
    diagReflectIndex N (-k-1) = diagReflectIndex N k := by
  apply Fin.ext
  simp only [diagReflectIndex, diagPeriodReflection_val hN]
  have hk := k.isLt
  split_ifs <;> omega

theorem diagReflectSign_reflection {N : ℕ} (hN : 0 < N) [NeZero (2*N)] (k : Fin (2*N)) :
    diagReflectSign N (-k-1) = -diagReflectSign N k := by
  simp only [diagReflectSign, diagPeriodReflection_val hN]
  have hk := k.isLt
  split_ifs <;> norm_num <;> omega

/-- Linear reflection in one grid coordinate. -/
def diagPeriodLinearReflection (N : ℕ) [NeZero (2*N)] (i : Fin 2) :
    (Fin 2 → Fin (2*N)) →+ (Fin 2 → Fin (2*N)) where
  toFun k a := if a = i then -k a else k a
  map_zero' := by funext a; simp
  map_add' k l := by
    funext a
    by_cases ha : a = i <;> simp [ha, add_comm]

/-- Cell-center reflection through a parent face is kᵢ↦−kᵢ−1. -/
def diagPeriodReflection (N : ℕ) [NeZero (2*N)] (i : Fin 2) (k : Fin 2 → Fin (2*N)) :
    Fin 2 → Fin (2*N) := fun a => if a = i then -k a-1 else k a

/-- The actual source odd extension is odd through both parent faces. -/
theorem diagOddGrid_reflection {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (m : (Fin 2 → Fin N) → ℝ) (i : Fin 2) (k : Fin 2 → Fin (2*N)) :
    diagOddGrid N m (diagPeriodReflection N i k) = -diagOddGrid N m k := by
  have hfold : (fun a => diagReflectIndex N (diagPeriodReflection N i k a)) =
      fun a => diagReflectIndex N (k a) := by
    funext a
    by_cases ha : a = i
    · simp only [diagPeriodReflection, ha, ite_true, diagReflectIndex_reflection hN]
    · simp only [diagPeriodReflection, ha, ite_false]
  unfold diagOddGrid
  rw [hfold]
  fin_cases i <;> simp [diagPeriodReflection, diagReflectSign_reflection hN]

/-- The two half-period embeddings are reflected copies. -/
theorem diagReflectionEquiv_inr_eq {N : ℕ} (hN : 0 < N) [NeZero (2*N)] (k : Fin N) :
    diagReflectionEquiv N (Sum.inr k) = -diagReflectionEquiv N (Sum.inl k)-1 := by
  apply Fin.ext
  rw [diagPeriodReflection_val hN]
  rfl

/-- A reflection-invariant row has exactly twice its original-cell sum. -/
theorem diagPeriod_even_sum {N : ℕ} (hN : 0 < N) [NeZero (2*N)]
    (F : Fin (2*N) → ℝ) (hF : ∀ k, F (-k-1) = F k) :
    (∑ k, F k) = 2 * ∑ k : Fin N, F (diagReflectionEquiv N (Sum.inl k)) := by
  rw [← Equiv.sum_comp (diagReflectionEquiv N) F, Fintype.sum_sum_type]
  simp_rw [diagReflectionEquiv_inr_eq hN, hF]
  ring

end

end ASDExplicitGamma.Triadic
