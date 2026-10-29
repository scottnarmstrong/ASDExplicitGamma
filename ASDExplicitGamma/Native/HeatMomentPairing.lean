module

public import ASDExplicitGamma.Native.HeatMomentAdjoint

/-! Exact cancellation of predecessor drift in backward moment pairing. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open scoped BigOperators
noncomputable section

/-- Forward and backward triangular rows are adjoint in the finite pairing.
The fixed zeroth coordinate is retained and its drift is zero. -/
theorem heat_moment_pairing_drift_eq (c t : ℝ) (k : ℕ) (m : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k+1),heatMomentTransition c k j t *
      (c*(j:ℝ)*m j+4*c*(j:ℝ)*m (j-1))) =
    ∑ j ∈ Finset.range (k+1),(c*(j:ℝ)*heatMomentTransition c k j t+
      4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) t)*m j := by
  have hoff : (∑ j ∈ Finset.range (k+1),heatMomentTransition c k j t*(4*c*(j:ℝ)*m (j-1))) =
      ∑ j ∈ Finset.range (k+1),4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) t*m j := by
    calc
      _ = ∑ j ∈ Finset.range k,heatMomentTransition c k (j+1) t*(4*c*(j+1:ℕ)*m j) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.add_sub_cancel,Nat.cast_zero,mul_zero,zero_mul,add_zero]
      _ = ∑ j ∈ Finset.range k,4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) t*m j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        rw [Finset.sum_range_succ,heat_moment_transition_eq_zero c k (k+1) (by omega) t]
        simp
  calc
    _ = (∑ j ∈ Finset.range (k+1),c*(j:ℝ)*heatMomentTransition c k j t*m j) +
        (∑ j ∈ Finset.range (k+1),heatMomentTransition c k j t*(4*c*(j:ℝ)*m (j-1))) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [hoff,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring

end
end ASDExplicitGamma.Native
