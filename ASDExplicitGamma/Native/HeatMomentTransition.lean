module

public import ASDExplicitGamma.Native.HeatMomentKernelDerivative

/-! Exact binomial transition entries for the affine moment system. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

def heatMomentTransition (c : ℝ) (k j : ℕ) (t : ℝ) : ℝ :=
  (Nat.choose k j:ℝ)*heatMomentGreenKernel c j (k-j) t

/-- Diagonal transition entries are the scalar exponential flow. -/
theorem heat_moment_transition_diagonal_hasDerivAt (c : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (heatMomentTransition c k k) (c*(k:ℝ)*heatMomentTransition c k k t) t := by
  convert heat_moment_green_kernel_hasDerivAt_zero c k t using 1
  · funext s
    simp [heatMomentTransition]
  · simp [heatMomentTransition]

/-- Positivity needed when every later-shear forcing term is integrated. -/
theorem heat_moment_transition_nonneg (c : ℝ) (hc : 0 ≤ c) (k j : ℕ)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ heatMomentTransition c k j t := by
  have hinc : 0 ≤ Real.exp (c*t)-1 := sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc ht))
  unfold heatMomentTransition heatMomentGreenKernel
  positivity

end
end ASDExplicitGamma.Native
