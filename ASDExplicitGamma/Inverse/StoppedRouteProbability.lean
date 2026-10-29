module

public import ASDExplicitGamma.Inverse.StoppedMarkControl
public import ASDExplicitGamma.Inverse.StoppedRouteCharge
public import ASDExplicitGamma.Inverse.StoppedGroupCharge

/-! Uniform finite-label probability estimates on the actual fixed route populations. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The finite-label source route charge has a uniform exponential moment,
with actual mark probabilities and only within-group restriction independence. -/
theorem control_route_charge_mgf {Ω : Type*} [MeasurableSpace Ω] {nv : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (v : Fin nv → BlockSite) (hv : RouteParitySeparated v) (N : ℕ) :
    Integrable (fun ω => Real.exp (5*routeCharge B v N ω)) μ ∧
    (∫ ω, Real.exp (5*routeCharge B v N ω) ∂μ) ≤ Real.exp ((nv:ℝ)/10) := by
  have hh := marked_charge_mgf (RouteGroupIndex v N) μ (routeGroupEvent B v N)
    (route_group_event_measurable B hB.local_measurable hB.positive_measurable v N)
    (control_route_group_independent μ B q hB v hv N)
    (markGroupWeight N) (routeGroupCoefficient N) (routeGroupProbability N q)
    (mark_group_weight_pos N) (mark_group_weights_sum N)
    (route_group_coefficient_nonneg N) (nv:ℝ)
    (control_route_group_probability μ B q hB v N)
    (route_group_scalar_cost N q hq0 hq)
    (fun g => by exact_mod_cast route_group_card_le v N g)
  simpa only [route_group_charge_eq] using! hh

/-- The source path charge has its exponential tail uniformly in the finite
label cutoff; no stopped-radius conclusion is an input. -/
theorem control_route_charge_tail {Ω : Type*} [MeasurableSpace Ω] {nv : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (v : Fin nv → BlockSite) (hv : RouteParitySeparated v) (N : ℕ) :
    μ.real {ω | (nv:ℝ) ≤ routeCharge B v N ω} ≤ Real.exp (-(49/10:ℝ)*(nv:ℝ)) := by
  obtain ⟨hi,hb⟩ := control_route_charge_mgf μ B q hB hq0 hq v hv N
  exact marked_charge_tail μ (routeCharge B v N) (nv:ℝ) hi hb

end
end ASDExplicitGamma.Inverse
