module

public import ASDExplicitGamma.Native.HeatPassBudget
public import ASDExplicitGamma.Native.HeatBracketRedistribution

/-! One complete differential-to-producer moment step, before the certified root. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- Nonnegativity of every positive-degree forcing row, including its bracket. -/
theorem heat_pass_forcing_nonneg (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed : List ℚ) (y : ℚ) (k : ℕ) (he : 0 ≤ old.e) (hx : 0 ≤ frames.x)
    (hy : 0 ≤ y) (hfixed : 0 ≤ fixed.getD (k-1) 0) :
    0 ≤ nativeHeatForcingAt old frames fixed y k := by
  rw [nativeHeatForcingAt_eq_explicit_remainder]
  exact (add_nonneg hfixed (nativeHeatBracketRemainderAt_nonneg old frames y k he hx hy)).trans (nativeUp_ge _)

/-- The complete triangular differential row implies the literal producer's
rounded moment budget. No pass improvement is assumed in this theorem. -/
theorem heat_pass_moment_bound (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed init : List ℚ) (y c ee : ℚ) (hc : 0 ≤ c)
    (hcheck : nativeHeatExpCheck c ee = true)
    (he : 0 ≤ old.e) (hx : 0 ≤ frames.x) (hy : 0 ≤ y)
    (hfixed : ∀ j < 20,0 ≤ fixed.getD j 0)
    (hinitlen : init.length = 21) (hinit0 : ∀ j ≤ 20,0 ≤ init.getD j 0)
    (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (m mp : ℕ → ℝ → ℝ)
    (hmcont : ∀ j ≤ 20,ContinuousOn (m j) (Icc 0 T))
    (hmderiv : ∀ s ∈ Ioo 0 T,∀ j ≤ 20,HasDerivAt (m j) (mp j s) s)
    (hint : IntervalIntegrable (heatMomentBackwardDerivative c 20 T m mp) volume 0 T)
    (hstart : ∀ j ≤ 20,m j 0 ≤ (init.getD j 0:ℝ))
    (hrow : ∀ s ∈ Icc 0 T,∀ j ≤ 20,mp j s ≤ (c:ℝ)*(j:ℝ)*m j s+4*(c:ℝ)*(j:ℝ)*m (j-1) s+
      (if j=0 then 0 else (nativeHeatForcingAt old frames fixed y j:ℝ))) :
    m 20 T ≤ (heatPassMomentBudget old frames (nativeHeatCoefficients ee) fixed
      (nativeHeatBase (nativeHeatCoefficients ee) init) y:ℝ) := by
  let coef := nativeHeatCoefficients ee
  let E : ℕ → ℝ := fun j => if j=0 then 0 else (nativeHeatForcingAt old frames fixed y j:ℝ)
  have hcR : (0:ℝ) ≤ c := by exact_mod_cast hc
  have hE (j : ℕ) (hj : j ≤ 20) : 0 ≤ E j := by
    by_cases hj0 : j=0
    · simp [E,hj0]
    · simp only [E,ite_eq_right hj0]
      exact_mod_cast heat_pass_forcing_nonneg old frames fixed y j he hx hy (hfixed (j-1) (by omega))
  have hinitR (j : ℕ) (hj : j ≤ 20) : (0:ℝ) ≤ init.getD j 0 := by exact_mod_cast hinit0 j hj
  have hweight (j : ℕ) (hj : j ≤ 20) : heatMomentTransition c 20 j 1 ≤ (coef.getD j 0:ℝ) :=
    heat_moment_transition_le_rounded_coefficient c ee hc hcheck j hj
  have hu := heat_moment_uniform_bound c hcR 20 T hT0 hT1 m mp E (fun j => (init.getD j 0:ℝ))
    hmcont hmderiv hint hrow hstart hinitR hE
  have hbase : (∑ j ∈ Finset.range 21,heatMomentTransition c 20 j 1*(init.getD j 0:ℝ)) ≤
      (nativeHeatBase coef init:ℝ) := by
    apply le_trans _ (heat_initial_sum_le_rounded_base coef init (by simp [coef,nativeHeatCoefficients]) hinitlen)
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ 20 := by have := Finset.mem_range.mp hj; omega
    exact mul_le_mul_of_nonneg_right (hweight j hj') (hinitR j hj')
  have hforce : (∑ j ∈ Finset.range 21,heatMomentTransition c 20 j 1*E j/(20-j+1:ℕ)) ≤
      ∑ j ∈ Finset.range 21,(coef.getD j 0:ℝ)*E j/(21-j:ℕ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j ≤ 20 := by have := Finset.mem_range.mp hj; omega
    rw [show 20-j+1=21-j by omega]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hweight j hj') (hE j hj')) (by positivity)
  have hbudget : (nativeHeatBase coef init:ℝ)+
      (∑ j ∈ Finset.range 21,(coef.getD j 0:ℝ)*E j/(21-j:ℕ)) ≤
      (heatPassMomentBudget old frames coef fixed (nativeHeatBase coef init) y:ℝ) := by
    dsimp [E]
    have hb := (Rat.cast_le (K := ℝ)).2 (heat_pass_budget_ge old frames coef fixed (nativeHeatBase coef init) y)
    push_cast at hb
    simpa only [apply_ite,Rat.cast_zero] using hb
  exact (hu.trans (add_le_add hbase hforce)).trans hbudget

end
end ASDExplicitGamma.Native
