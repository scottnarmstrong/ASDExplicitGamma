module

public import ASDExplicitGamma.Inverse.StoppedRouteGroups
public import ASDExplicitGamma.Inverse.StoppedMarkedField
public import ASDExplicitGamma.Inverse.StoppedMarkCosts

/-! Literal events and scalar budgets attached to the actual route subpopulations. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Each group observes actual source marks or actual aligned activations. -/
def routeGroupEvent {Ω : Type*} {nv : ℕ} (B : PlanarMarks Ω)
    (v : Fin nv → BlockSite) (N : ℕ) : (g : MarkGroup N) → RouteGroupIndex v N g → Set Ω
  | none, i => nomatch i
  | some (.inl _), i => B.localMark (v i.val)
  | some (.inr p), i => positiveActivation B p.1.val i.val

/-- The path charge coefficient is one for local sites and the literal side
for each positive aligned cube. The unused group has zero coefficient. -/
def routeGroupCoefficient (N : ℕ) : MarkGroup N → ℝ
  | none => 0
  | some (.inl _) => 1
  | some (.inr p) => positiveLabelSide p.1.val

/-- Exact probability budget of a complete activation cube, not just one raw mark. -/
def routeGroupProbability (N : ℕ) (q : ℝ) : MarkGroup N → ℝ
  | none => 0
  | some (.inl _) => q
  | some (.inr p) => (positiveLabelSide p.1.val)^2*
      Real.exp (-1200*positiveLabelSide p.1.val*Real.sqrt (positiveLabelSide p.1.val))

/-- Every group coefficient is nonnegative. -/
theorem route_group_coefficient_nonneg (N : ℕ) (g : MarkGroup N) :
    0 ≤ routeGroupCoefficient N g := by
  cases g with
  | none => exact le_rfl
  | some g =>
    cases g with
    | inl _ => exact zero_le_one
    | inr p => exact (positive_label_side_pos _).le

/-- The two local and nine positive color budgets fit a common conservative
per-path cost. This retains enough room for the final source radius constants. -/
theorem route_group_scalar_cost (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (g : MarkGroup N) :
    routeGroupProbability N q g*(Real.exp (5*routeGroupCoefficient N g/markGroupWeight N g)-1) ≤ 1/10 := by
  cases g with
  | none => simp [routeGroupProbability]
  | some g =>
    cases g with
    | inl _ =>
      norm_num only [routeGroupProbability,routeGroupCoefficient,markGroupWeight,mul_one,div_div]
      exact local_mark_tilt_cost q hq0 hq
    | inr p =>
      apply positive_mark_tilt_cost (positiveLabelSide p.1.val) (Real.sqrt (positiveLabelSide p.1.val))
        (5*positiveLabelSide p.1.val/(positiveLabelWeight p.1.val/9))
      · unfold positiveLabelSide
        have hh : (1:ℝ) ≤ 3^p.1.val := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        linarith only [hh]
      · exact Real.sqrt_nonneg _
      · exact Real.sq_sqrt (positive_label_side_pos _).le
      · exact positive_label_tilt_le _

/-- Positive activations are genuine measurable unions of the actual raw marks. -/
theorem positive_activation_measurable {Ω : Type*} [MeasurableSpace Ω] (B : PlanarMarks Ω)
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (n : ℕ) (i : BlockSite) :
    MeasurableSet (positiveActivation B n i) :=
  MeasurableSet.iUnion (fun x => MeasurableSet.iUnion (fun _hx => hP n x))

/-- Every fixed candidate group consists of actual measurable mark events. -/
theorem route_group_event_measurable {Ω : Type*} [MeasurableSpace Ω] {nv : ℕ}
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x))
    (v : Fin nv → BlockSite) (N : ℕ) (g : MarkGroup N) (i : RouteGroupIndex v N g) :
    MeasurableSet (routeGroupEvent B v N g i) := by
  cases g with
  | none => exact Empty.elim i
  | some g =>
    cases g with
    | inl c => exact hL (v i.val)
    | inr p => exact positive_activation_measurable B hP p.1.val i.val

end
end ASDExplicitGamma.Inverse
