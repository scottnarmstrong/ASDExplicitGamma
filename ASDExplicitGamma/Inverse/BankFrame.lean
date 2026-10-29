module

public import ASDExplicitGamma.Inverse.BankHistoryPopulation

/-! Exact deterministic frame shifts for the complete inverse histories. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3
open scoped ENNReal

theorem bank_history_frame_gap_shift (M : ABKModel 2) (Q : TriadicCube 2)
    (ell m : ℤ) (j : ℕ) (hQ : Q.scale ≤ ell) (hell : ell ≤ m) :
    ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((ell-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) := by
  have hm0 : (0:ℝ) ≤ ((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ) := by
    exact_mod_cast (show (0:ℤ) ≤ m-(Q.scale-(j:ℤ))+1 by omega)
  have hell0 : (0:ℝ) ≤ ((ell-(Q.scale-(j:ℤ))+1:ℤ):ℝ) := by
    exact_mod_cast (show (0:ℤ) ≤ ell-(Q.scale-(j:ℤ))+1 by omega)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  rw [abs_of_nonneg hm0, abs_of_nonneg hell0]
  push_cast
  ring

theorem bank_history_frame_gap_add (M : ABKModel 2) (Q : TriadicCube 2)
    (ell m : ℤ) (j : ℕ) (hQ : Q.scale = ell) (hell : ell ≤ m) :
    ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((ell-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) := by
  have he₁ : m-(Q.scale-(j:ℤ))+1 = (m-ell)+(j:ℤ)+1 := by rw [hQ]; ring
  have he₂ : ell-(Q.scale-(j:ℤ))+1 = (j:ℤ)+1 := by rw [hQ]; ring
  have hellR : (ell:ℝ) ≤ (m:ℝ) := by exact_mod_cast hell
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  rw [he₁, he₂]
  push_cast
  rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ)+1)]
  ring

theorem bank_history_series_mul (c : ℝ≥0∞) (f : ℕ → ℝ≥0∞) :
    bankHistoryPrefactor * (∑' j, bankHistoryAlpha^j * (c*f j)) =
      c * (bankHistoryPrefactor * ∑' j, bankHistoryAlpha^j*f j) := by
  have he (j : ℕ) : bankHistoryAlpha^j*(c*f j) = c*(bankHistoryAlpha^j*f j) := by
    ac_rfl
  simp_rw [he]
  rw [ENNReal.tsum_mul_left]
  ac_rfl

theorem bank_root_inverse_baseline_history_shift (M : ABKModel 2)
    (Q : TriadicCube 2) (ell m : ℤ) (r : RootRow)
    (hQ : Q.scale = ell) (hell : ell ≤ m) :
    bankRootInverseBaselineHistory Q M m r =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        bankRootInverseBaselineHistory Q M ell r := by
  have he (j : ℕ) : bankRootDepthBaseline M Q m r j =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        bankRootDepthBaseline M Q ell r j := by
    unfold bankRootDepthBaseline
    rw [bank_history_frame_gap_add M Q ell m j hQ hell]
    exact mul_assoc _ _ _
  unfold bankRootInverseBaselineHistory
  simp_rw [he]
  exact bank_history_series_mul _ _

theorem bank_root_inverse_remainder_history_budget_shift (M : ABKModel 2)
    (Q : TriadicCube 2) (ell m : ℤ) (r : RootRow)
    (hQ : Q.scale = ell) (hell : ell ≤ m) :
    bankRootInverseRemainderHistoryL256Bound M Q m r =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        bankRootInverseRemainderHistoryL256Bound M Q ell r := by
  let C := ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ)))
  let E := ENNReal.ofReal (rootLi M.gamma r*selectedRootTiny (rootH0 r)) +
    ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r+rootDensityErrorBudget M.gamma r)
  let F (n : ℤ) (j : ℕ) :=
    ((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
      (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((n-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|))*E)
  have he (j : ℕ) : F m j = C*F ell j := by
    dsimp only [F, C]
    rw [bank_history_frame_gap_add M Q ell m j hQ hell]
    ac_rfl
  change bankHistoryPrefactor*(∑' j, bankHistoryAlpha^j*F m j) =
    C*(bankHistoryPrefactor*∑' j, bankHistoryAlpha^j*F ell j)
  simp_rw [he]
  exact bank_history_series_mul _ _

theorem bank_root_inverse_baseline_history_frame_shift (M : ABKModel 2)
    (Q : TriadicCube 2) (ell m : ℤ) (r : RootRow)
    (hQ : Q.scale ≤ ell) (hell : ell ≤ m) :
    bankRootInverseBaselineHistory Q M m r =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        bankRootInverseBaselineHistory Q M ell r := by
  have he (j : ℕ) : bankRootDepthBaseline M Q m r j =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        bankRootDepthBaseline M Q ell r j := by
    unfold bankRootDepthBaseline
    rw [bank_history_frame_gap_shift M Q ell m j hQ hell]
    exact mul_assoc _ _ _
  unfold bankRootInverseBaselineHistory
  simp_rw [he]
  exact bank_history_series_mul _ _

theorem bank_root_inverse_remainder_history_budget_frame_shift (M : ABKModel 2)
    (Q : TriadicCube 2) (ell m : ℤ) (r : RootRow)
    (hQ : Q.scale ≤ ell) (hell : ell ≤ m) :
    bankRootInverseRemainderHistoryL256Bound M Q m r =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
        bankRootInverseRemainderHistoryL256Bound M Q ell r := by
  let C := ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ)))
  let E := ENNReal.ofReal (rootLi M.gamma r*selectedRootTiny (rootH0 r)) +
    ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r+rootDensityErrorBudget M.gamma r)
  let F (n : ℤ) (j : ℕ) :=
    ((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
      (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((n-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|))*E)
  have he (j : ℕ) : F m j = C*F ell j := by
    dsimp only [F, C]
    rw [bank_history_frame_gap_shift M Q ell m j hQ hell]
    ac_rfl
  change bankHistoryPrefactor*(∑' j, bankHistoryAlpha^j*F m j) =
    C*(bankHistoryPrefactor*∑' j, bankHistoryAlpha^j*F ell j)
  simp_rw [he]
  exact bank_history_series_mul _ _

theorem bank_root_frame_factor_shift (M : ABKModel 2) (Q : TriadicCube 2)
    (ell m : ℤ) (hQ : Q.scale ≤ ell) (hell : ell ≤ m) :
    bankRootFrameFactor M Q m = ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
      bankRootFrameFactor M Q ell := by
  simpa only [bankRootFrameFactor, Nat.cast_zero, sub_zero] using
    bank_history_frame_gap_shift M Q ell m 0 hQ hell

theorem bank_root_response_baseline_frame_shift (M : ABKModel 2) (Q : TriadicCube 2)
    (ell m : ℤ) (r : RootRow) (hQ : Q.scale ≤ ell) (hell : ell ≤ m) :
    bankRootResponseBaseline M Q m r = ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((m-ell:ℤ):ℝ))) *
      bankRootResponseBaseline M Q ell r := by
  unfold bankRootResponseBaseline
  rw [bank_root_frame_factor_shift M Q ell m hQ hell]
  exact mul_assoc _ _ _

end ASDExplicitGamma.Inverse
