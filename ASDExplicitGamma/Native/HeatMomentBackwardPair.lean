module

public import ASDExplicitGamma.Native.HeatMomentPairing

/-! Backward pairing retains the full forcing vector in every degree. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open scoped BigOperators
noncomputable section

def heatMomentBackwardPair (c : ℝ) (k : ℕ) (T : ℝ) (m : ℕ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),heatMomentTransition c k j (T-s)*m j s

def heatMomentBackwardDerivative (c : ℝ) (k : ℕ) (T : ℝ)
    (m mp : ℕ → ℝ → ℝ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),(heatMomentTransition c k j (T-s)*mp j s -
    (c*(j:ℝ)*heatMomentTransition c k j (T-s)+
      4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) (T-s))*m j s)

/-- Differentiation of the finite backward pairing, with no forcing removed. -/
theorem heat_moment_backward_pair_hasDerivAt (c : ℝ) (k : ℕ) (T s : ℝ)
    (m mp : ℕ → ℝ → ℝ)
    (hm : ∀ j ≤ k,HasDerivAt (m j) (mp j s) s) :
    HasDerivAt (heatMomentBackwardPair c k T m) (heatMomentBackwardDerivative c k T m mp s) s := by
  have hj (j : ℕ) (hj : j ∈ Finset.range (k+1)) :=
    (heat_moment_transition_adjoint_le c k j (by have := Finset.mem_range.mp hj; omega) (T-s)).comp s
      ((hasDerivAt_const s T).sub (hasDerivAt_id s))
  have hterm (j : ℕ) (hj' : j ∈ Finset.range (k+1)) :
      HasDerivAt (fun r => heatMomentTransition c k j (T-r)*m j r)
        (heatMomentTransition c k j (T-s)*mp j s -
          (c*(j:ℝ)*heatMomentTransition c k j (T-s)+
            4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) (T-s))*m j s) s := by
    have h := (hj j hj').mul (hm j (by have := Finset.mem_range.mp hj'; omega))
    convert h using 1
    · funext r
      rfl
    · simp only [Function.comp_apply]
      ring
  have hh := HasDerivAt.fun_sum hterm
  exact hh

/-- The complete source row bounds the pairing derivative by precisely its
forcing vector. This is where all predecessor contributions cancel. -/
theorem heat_moment_backward_derivative_le (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (T s : ℝ)
    (hs : s ≤ T) (m mp : ℕ → ℝ → ℝ) (E : ℕ → ℝ)
    (hrow : ∀ j ≤ k,mp j s ≤ c*(j:ℝ)*m j s + 4*c*(j:ℝ)*m (j-1) s + E j) :
    heatMomentBackwardDerivative c k T m mp s ≤
      ∑ j ∈ Finset.range (k+1),heatMomentTransition c k j (T-s)*E j := by
  unfold heatMomentBackwardDerivative
  calc
    _ ≤ ∑ j ∈ Finset.range (k+1),(heatMomentTransition c k j (T-s)*
        (c*(j:ℝ)*m j s+4*c*(j:ℝ)*m (j-1) s+E j) -
        (c*(j:ℝ)*heatMomentTransition c k j (T-s)+
          4*c*(j+1:ℕ)*heatMomentTransition c k (j+1) (T-s))*m j s) := by
      apply Finset.sum_le_sum
      intro j hj
      apply sub_le_sub_right
      exact mul_le_mul_of_nonneg_left (hrow j (by have := Finset.mem_range.mp hj; omega))
        (heat_moment_transition_nonneg c hc k j (T-s) (sub_nonneg.mpr hs))
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_add_distrib]
      have hp := heat_moment_pairing_drift_eq c (T-s) k (fun j => m j s)
      simp_rw [mul_add] at hp
      rw [Finset.sum_add_distrib] at hp
      linarith only [hp]

end
end ASDExplicitGamma.Native
