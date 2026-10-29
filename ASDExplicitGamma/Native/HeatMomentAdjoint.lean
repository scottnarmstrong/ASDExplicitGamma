module

public import ASDExplicitGamma.Native.HeatMomentTransition

/-! Backward-kernel identities for retaining all forcing degrees. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Equivalent column form of the affine kernel equation. -/
theorem heat_moment_green_kernel_adjoint (c : ℝ) (j d : ℕ) (t : ℝ) :
    HasDerivAt (heatMomentGreenKernel c j (d+1))
      (c*(j:ℝ)*heatMomentGreenKernel c j (d+1) t +
        4*c*(d+1:ℕ)*heatMomentGreenKernel c (j+1) d t) t := by
  convert heat_moment_green_kernel_hasDerivAt_succ c j d t using 1
  unfold heatMomentGreenKernel
  simp only [pow_succ,Nat.cast_add,Nat.cast_one]
  ring

/-- The column equation cancels the predecessor drift when the backward
transition is paired with the complete forward moment vector. -/
theorem heat_moment_transition_adjoint (c : ℝ) (k j : ℕ) (hj : j < k) (t : ℝ) :
    HasDerivAt (heatMomentTransition c k j)
      (c*(j:ℝ)*heatMomentTransition c k j t +
        4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) t) t := by
  have hd : k-j = (k-j-1)+1 := by omega
  have hd' : k-(j+1) = k-j-1 := by omega
  have hnR : (Nat.choose k (j+1):ℝ)*(j+1:ℕ) = (Nat.choose k j:ℝ)*((k-j-1)+1:ℕ) := by
    exact_mod_cast (show Nat.choose k (j+1)*(j+1)=Nat.choose k j*((k-j-1)+1) by
      rw [←hd]; exact Nat.choose_succ_right_eq k j)
  have hh := (heat_moment_green_kernel_adjoint c j (k-j-1) t).const_mul (Nat.choose k j:ℝ)
  convert hh using 1
  · funext s
    simp only [heatMomentTransition]
    rw [←hd]
  · unfold heatMomentTransition
    rw [←hd,hd']
    rw [←hd] at hnR
    linear_combination 4*c*heatMomentGreenKernel c (j+1) (k-j-1) t*hnR

/-- Transition entries above the diagonal vanish identically. -/
theorem heat_moment_transition_eq_zero (c : ℝ) (k j : ℕ) (hj : k < j) (t : ℝ) :
    heatMomentTransition c k j t = 0 := by
  simp [heatMomentTransition,Nat.choose_eq_zero_of_lt hj]

/-- Uniform column equation, including the top degree and its zero successor. -/
theorem heat_moment_transition_adjoint_le (c : ℝ) (k j : ℕ) (hj : j ≤ k) (t : ℝ) :
    HasDerivAt (heatMomentTransition c k j)
      (c*(j:ℝ)*heatMomentTransition c k j t +
        4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) t) t := by
  rcases lt_or_eq_of_le hj with hlt | rfl
  · exact heat_moment_transition_adjoint c k j hlt t
  · simpa only [heat_moment_transition_eq_zero c j (j+1) (by omega) t,mul_zero,add_zero] using
      heat_moment_transition_diagonal_hasDerivAt c j t

/-- Identity initial transition, with all forcing degrees retained. -/
theorem heat_moment_transition_zero_time (c : ℝ) (k j : ℕ) :
    heatMomentTransition c k j 0 = if j=k then 1 else 0 := by
  by_cases he : j=k
  · subst j
    simp [heatMomentTransition,heatMomentGreenKernel]
  · by_cases hj : j < k
    · have hd : k-j ≠ 0 := by omega
      simp [heatMomentTransition,heatMomentGreenKernel,he,hd]
    · rw [heat_moment_transition_eq_zero c k j (by omega)]
      simp [he]

end
end ASDExplicitGamma.Native
