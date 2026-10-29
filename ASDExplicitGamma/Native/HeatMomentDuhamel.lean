module

public import ASDExplicitGamma.Native.HeatMomentBackwardPair

/-! Duhamel bound for the complete triangular affine moment recurrence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- Continuous transition coefficients, including all off-diagonal degrees. -/
theorem heat_moment_transition_continuous (c : ℝ) (k j : ℕ) :
    Continuous (heatMomentTransition c k j) := by
  unfold heatMomentTransition heatMomentGreenKernel
  fun_prop

theorem heat_moment_backward_pair_terminal (c : ℝ) (k : ℕ) (T : ℝ) (m : ℕ → ℝ → ℝ) :
    heatMomentBackwardPair c k T m T = m k T := by
  unfold heatMomentBackwardPair
  simp [heat_moment_transition_zero_time,Finset.sum_ite_eq']

/-- The actual recurrence implies the full Duhamel bound. Continuity and
integrability are explicit analytic hypotheses here; source consumers must
supply them for their actual moment curve, rather than assuming this bound. -/
theorem heat_moment_duhamel (c : ℝ) (hc : 0 ≤ c) (k : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (m mp : ℕ → ℝ → ℝ) (E : ℕ → ℝ)
    (hmcont : ∀ j ≤ k,ContinuousOn (m j) (Icc 0 T))
    (hmderiv : ∀ s ∈ Ioo 0 T,∀ j ≤ k,HasDerivAt (m j) (mp j s) s)
    (hint : IntervalIntegrable (heatMomentBackwardDerivative c k T m mp) volume 0 T)
    (hrow : ∀ s ∈ Icc 0 T,∀ j ≤ k,mp j s ≤ c*(j:ℝ)*m j s+4*c*(j:ℝ)*m (j-1) s+E j) :
    m k T ≤ (∑ j ∈ Finset.range (k+1),heatMomentTransition c k j T*m j 0) +
      ∫ s in (0:ℝ)..T,∑ j ∈ Finset.range (k+1),heatMomentTransition c k j (T-s)*E j := by
  have hpc : ContinuousOn (heatMomentBackwardPair c k T m) (Icc 0 T) := by
    apply continuousOn_finsetSum
    intro j hj
    exact ((heat_moment_transition_continuous c k j).comp
      (continuous_const.sub continuous_id)).continuousOn.mul
        (hmcont j (by have := Finset.mem_range.mp hj; omega))
  have hpd : ∀ s ∈ Ioo 0 T,HasDerivAt (heatMomentBackwardPair c k T m)
      (heatMomentBackwardDerivative c k T m mp s) s := fun s hs =>
    heat_moment_backward_pair_hasDerivAt c k T s m mp (hmderiv s hs)
  have hfc : Continuous (fun s : ℝ => ∑ j ∈ Finset.range (k+1),heatMomentTransition c k j (T-s)*E j) := by
    apply continuous_finsetSum
    intro j _
    exact ((heat_moment_transition_continuous c k j).comp
      (continuous_const.sub continuous_id)).mul continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hpc hpd hint
  have hbound := intervalIntegral.integral_mono_on hT hint (hfc.intervalIntegrable 0 T)
    (fun s hs => heat_moment_backward_derivative_le c hc k T s hs.2 m mp E (hrow s hs))
  rw [hftc,heat_moment_backward_pair_terminal] at hbound
  have hstart : heatMomentBackwardPair c k T m 0 =
      ∑ j ∈ Finset.range (k+1),heatMomentTransition c k j T*m j 0 := by
    simp only [heatMomentBackwardPair,sub_zero]
  rw [hstart] at hbound
  linarith only [hbound]

end
end ASDExplicitGamma.Native
