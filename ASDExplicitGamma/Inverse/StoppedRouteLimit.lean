module

public import ASDExplicitGamma.Inverse.StoppedRouteProbability
public import Mathlib.MeasureTheory.Measure.Continuity

/-! The actual finite-label marked charge retains its probability bound in the infinite-label field. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- Finite label charges increase because every activation payment is nonnegative. -/
theorem route_charge_mono {Ω : Type*} {nv : ℕ} (B : PlanarMarks Ω)
    (v : Fin nv → BlockSite) (ω : Ω) : Monotone (fun N => routeCharge B v N ω) := by
  intro N M hNM
  apply add_le_add le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
  intro n _ _
  exact mul_nonneg (positive_label_side_pos n).le
    (Finset.sum_nonneg (fun i _ => (mark_indicator_bounds _ _).1))

/-- An increasing sequence of actual events retains a uniform finite probability cap. -/
theorem increasing_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω) (hE : Monotone E)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ N, μ.real (E N) ≤ C) :
    μ.real (⋃ N, E N) ≤ C := by
  have hn (N : ℕ) : μ (E N) ≤ ENNReal.ofReal C := by
    rw [← ofReal_measureReal (μ := μ) (s := E N) (by finiteness)]
    exact ENNReal.ofReal_le_ofReal (hb N)
  have hh : μ (⋃ N, E N) ≤ ENNReal.ofReal C := by
    rw [hE.measure_iUnion]
    exact iSup_le hn
  exact (ENNReal.toReal_mono (by simp) hh).trans_eq (ENNReal.toReal_ofReal hC)

/-- The full source charge event, allowing an arbitrary finite witness label
cutoff selected from the sample, retains the same exponential probability. -/
theorem control_route_full_charge_tail {Ω : Type*} [MeasurableSpace Ω] {nv : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (v : Fin nv → BlockSite) (hv : RouteParitySeparated v) :
    μ.real {ω | ∃ N, (nv:ℝ) ≤ routeCharge B v N ω} ≤ Real.exp (-(49/10:ℝ)*(nv:ℝ)) := by
  let E (N : ℕ) : Set Ω := {ω | (nv:ℝ) ≤ routeCharge B v N ω}
  have hm : Monotone E := by
    intro N M hNM ω hω
    exact hω.trans (route_charge_mono B v ω hNM)
  have hh := increasing_event_bound μ E hm _ (Real.exp_pos _).le
    (fun N => control_route_charge_tail μ B q hB hq0 hq v hv N)
  simpa only [E,Set.iUnion_ofPred] using hh

end
end ASDExplicitGamma.Inverse
