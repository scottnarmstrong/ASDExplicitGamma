module

public import ASDExplicitGamma.Native.HeatPassMomentBound

/-! Soundness of one finite heat-cap improvement, including its certified root. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native MeasureTheory Set
noncomputable section

/-- A nonnegative cap for the actual twentieth moment over the whole path. -/
def HeatUniformMomentCap (m : ℕ → ℝ → ℝ) (y : ℚ) : Prop :=
  0 ≤ y ∧ ∀ t ∈ Icc (0:ℝ) 1,m 20 t ≤ (y:ℝ)^20

/-- Taking the minimum preserves BOTH proved pathwise-in-time caps; the
second one comes from the complete rounded moment budget and checked root. -/
theorem heat_pass_uniform_cap_of_budget (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base y : ℚ) (m : ℕ → ℝ → ℝ)
    (hy : HeatUniformMomentCap m y)
    (hbudget : ∀ t ∈ Icc (0:ℝ) 1,m 20 t ≤ (heatPassMomentBudget old frames coef fixed base y:ℝ))
    (hroot : nativeRootValid (heatPassMomentBudget old frames coef fixed base y) 20 = true) :
    HeatUniformMomentCap m (nativeHeatPass old frames coef fixed base y) := by
  have hr : 0 < 20 ∧ 0 ≤ heatPassMomentBudget old frames coef fixed base y ∧
      0 ≤ nativeRootUp (heatPassMomentBudget old frames coef fixed base y) 20 ∧
      heatPassMomentBudget old frames coef fixed base y ≤
        (nativeRootUp (heatPassMomentBudget old frames coef fixed base y) 20)^20 := of_decide_eq_true hroot
  rw [heat_pass_eq_min_root]
  refine ⟨le_min hy.1 hr.2.2.1,?_⟩
  intro t ht
  by_cases hmin : y ≤ nativeRootUp (heatPassMomentBudget old frames coef fixed base y) 20
  · rw [min_eq_left hmin]
    exact hy.2 t ht
  · rw [min_eq_right (le_of_not_ge hmin)]
    exact (hbudget t ht).trans (by exact_mod_cast hr.2.2.2)

/-- The differential recurrence proves one actual uniform-cap improvement.
No output cap or moment budget inequality is assumed. -/
theorem heat_pass_uniform_cap (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed init : List ℚ) (y c ee : ℚ) (hc : 0 ≤ c)
    (hcheck : nativeHeatExpCheck c ee = true)
    (he : 0 ≤ old.e) (hx : 0 ≤ frames.x)
    (hfixed : ∀ j < 20,0 ≤ fixed.getD j 0)
    (hinitlen : init.length = 21) (hinit0 : ∀ j ≤ 20,0 ≤ init.getD j 0)
    (m mp : ℕ → ℝ → ℝ) (hy : HeatUniformMomentCap m y)
    (hmcont : ∀ j ≤ 20,ContinuousOn (m j) (Icc 0 1))
    (hmderiv : ∀ s ∈ Ioo 0 1,∀ j ≤ 20,HasDerivAt (m j) (mp j s) s)
    (hint : ∀ T ∈ Icc (0:ℝ) 1,IntervalIntegrable (heatMomentBackwardDerivative c 20 T m mp) volume 0 T)
    (hstart : ∀ j ≤ 20,m j 0 ≤ (init.getD j 0:ℝ))
    (hrow : ∀ s ∈ Icc 0 1,∀ j ≤ 20,mp j s ≤ (c:ℝ)*(j:ℝ)*m j s+4*(c:ℝ)*(j:ℝ)*m (j-1) s+
      (if j=0 then 0 else (nativeHeatForcingAt old frames fixed y j:ℝ)))
    (hroot : nativeRootValid (heatPassMomentBudget old frames (nativeHeatCoefficients ee) fixed
      (nativeHeatBase (nativeHeatCoefficients ee) init) y) 20 = true) :
    HeatUniformMomentCap m (nativeHeatPass old frames (nativeHeatCoefficients ee) fixed
      (nativeHeatBase (nativeHeatCoefficients ee) init) y) := by
  apply heat_pass_uniform_cap_of_budget old frames _ fixed _ y m hy _ hroot
  intro T hT
  apply heat_pass_moment_bound old frames fixed init y c ee hc hcheck he hx hy.1 hfixed hinitlen hinit0
    T hT.1 hT.2 m mp
  · intro j hj
    exact (hmcont j hj).mono (fun s hs => ⟨hs.1,hs.2.trans hT.2⟩)
  · intro s hs j hj
    exact hmderiv s ⟨hs.1,hs.2.trans_le hT.2⟩ j hj
  · exact hint T hT
  · exact hstart
  · intro s hs j hj
    exact hrow s ⟨hs.1,hs.2.trans hT.2⟩ j hj

end
end ASDExplicitGamma.Native
