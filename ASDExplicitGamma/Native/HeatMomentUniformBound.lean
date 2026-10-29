module

public import ASDExplicitGamma.Native.HeatMomentDuhamel

/-! Uniform finite-time moment bounds with the source Green weights. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem heat_moment_transition_mono_time (c : ℝ) (hc : 0 ≤ c) (k j : ℕ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    heatMomentTransition c k j s ≤ heatMomentTransition c k j t := by
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hc)
  have hi : 0 ≤ Real.exp (c*s)-1 := sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc hs))
  unfold heatMomentTransition heatMomentGreenKernel
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact mul_le_mul (pow_le_pow_left₀ (Real.exp_nonneg _) he j)
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (sub_le_sub_right he 1) (by norm_num : (0:ℝ)≤4)) (k-j))
    (pow_nonneg (by positivity) _) (pow_nonneg (Real.exp_nonneg _) _)

/-- The positive forcing weights are uniform on the entire heat interval.
Their denominator is the source's exact degree difference plus one. -/
theorem heat_moment_full_forcing_bound (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (T : ℝ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (E : ℕ → ℝ) (hE : ∀ j ≤ k,0 ≤ E j) :
    (∫ s in (0:ℝ)..T,∑ j ∈ Finset.range (k+1),heatMomentTransition c k j (T-s)*E j) ≤
      ∑ j ∈ Finset.range (k+1),heatMomentTransition c k j 1*E j/(k-j+1:ℕ) := by
  have hi (j : ℕ) (_hj : j ∈ Finset.range (k+1)) :
      IntervalIntegrable (fun s => heatMomentTransition c k j (T-s)*E j) volume 0 T :=
    (((heat_moment_transition_continuous c k j).comp
      (continuous_const.sub continuous_id)).mul continuous_const).intervalIntegrable 0 T
  rw [intervalIntegral.integral_finsetSum hi]
  apply Finset.sum_le_sum
  intro j hj
  have hEj := hE j (by have := Finset.mem_range.mp hj; omega)
  have hh := heat_moment_green_degree_bound c hc k j (E j) T hEj hT0 hT1
  have hid : (fun s => heatMomentTransition c k j (T-s)*E j) =
      (fun s => (Nat.choose k j:ℝ)*E j*heatMomentGreenKernel c j (k-j) (T-s)) := by
    funext s
    unfold heatMomentTransition
    ring
  rw [hid]
  simpa only [heatMomentTransition,heatMomentGreenKernel,mul_one,mul_assoc] using hh

/-- Complete uniform moment estimate from the actual differential rows.
Each retained forcing degree is paid once by its exact positive Green weight. -/
theorem heat_moment_uniform_bound (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (T : ℝ)
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (m mp : ℕ → ℝ → ℝ) (E init : ℕ → ℝ)
    (hmcont : ∀ j ≤ k,ContinuousOn (m j) (Icc 0 T))
    (hmderiv : ∀ s ∈ Ioo 0 T,∀ j ≤ k,HasDerivAt (m j) (mp j s) s)
    (hint : IntervalIntegrable (heatMomentBackwardDerivative c k T m mp) volume 0 T)
    (hrow : ∀ s ∈ Icc 0 T,∀ j ≤ k,mp j s ≤ c*(j:ℝ)*m j s+4*c*(j:ℝ)*m (j-1) s+E j)
    (hinit : ∀ j ≤ k,m j 0 ≤ init j) (hinit0 : ∀ j ≤ k,0 ≤ init j)
    (hE : ∀ j ≤ k,0 ≤ E j) :
    m k T ≤ (∑ j ∈ Finset.range (k+1),heatMomentTransition c k j 1*init j) +
      ∑ j ∈ Finset.range (k+1),heatMomentTransition c k j 1*E j/(k-j+1:ℕ) := by
  have hd := heat_moment_duhamel c hc k T hT0 m mp E hmcont hmderiv hint hrow
  apply hd.trans
  apply add_le_add _ (heat_moment_full_forcing_bound c hc k T hT0 hT1 E hE)
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := by have := Finset.mem_range.mp hj; omega
  exact (mul_le_mul_of_nonneg_left (hinit j hjk) (heat_moment_transition_nonneg c hc k j T hT0)).trans
    (mul_le_mul_of_nonneg_right (heat_moment_transition_mono_time c hc k j T 1 hT0 hT1) (hinit0 j hjk))

end
end ASDExplicitGamma.Native
