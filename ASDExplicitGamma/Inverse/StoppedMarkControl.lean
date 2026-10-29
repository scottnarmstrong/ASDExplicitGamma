module

public import ASDExplicitGamma.Inverse.StoppedRouteGroupEvents
public import ASDExplicitGamma.Inverse.StoppedIndependentMarks

/-! The named mark-probability and restriction-independence inputs to the cluster proof. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory

/-- The source inputs, separated from every cluster/path/radius conclusion.
The physical q3 application supplies these from old-history Markov, the proved
wave gate, and independence of entire separated restriction families. -/
structure PlanarMarkControl {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : PlanarMarks Ω) (q : ℝ) : Prop where
  local_measurable : ∀ x, MeasurableSet (B.localMark x)
  positive_measurable : ∀ n x, MeasurableSet (B.positiveMark n x)
  local_probability : ∀ x, μ.real (B.localMark x) ≤ q
  positive_probability : ∀ n x, μ.real (B.positiveMark n x) ≤
    Real.exp (-1200*positiveLabelSide n*Real.sqrt (positiveLabelSide n))
  local_independent : ∀ {I : Type} [Fintype I] (x : I → BlockSite),
    (Pairwise fun i j => ∃ d, 1 < |x j d-x i d|) →
      iIndepFun (fun i => markIndicator (B.localMark (x i))) μ
  positive_independent : ∀ n {I : Type} [Fintype I] (x : I → BlockSite) (c : Fin 9),
    Function.Injective x → (∀ i, blockColor (x i) = c) →
      iIndepFun (fun i => markIndicator (positiveActivation B n (x i))) μ

/-- The actual activation cube receives its exact side-squared raw probability cost. -/
theorem control_activation_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (n : ℕ) (i : BlockSite) :
    μ.real (positiveActivation B n i) ≤ (positiveLabelSide n)^2*
      Real.exp (-1200*positiveLabelSide n*Real.sqrt (positiveLabelSide n)) := by
  have hh := cube_activation_probability μ (B.positiveMark n)
    (alignedCubeBase (3^(n+1)) i) (3^(n+1)) _ (hB.positive_probability n)
  simpa only [positiveLabelSide,Nat.cast_pow,Nat.cast_ofNat] using! hh

/-- The deterministic same-parity separation condition on a fixed candidate route. -/
def RouteParitySeparated {nv : ℕ} (v : Fin nv → BlockSite) : Prop :=
  ∀ i j, i ≠ j → i.val%2 = j.val%2 → ∃ d, 1 < |v j d-v i d|

/-- The probability inputs are instantiated on each actual finite candidate group. -/
theorem control_route_group_probability {Ω : Type*} [MeasurableSpace Ω] {nv : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (v : Fin nv → BlockSite) (N : ℕ)
    (g : MarkGroup N) (i : RouteGroupIndex v N g) :
    μ.real (routeGroupEvent B v N g i) ≤ routeGroupProbability N q g := by
  cases g with
  | none => exact Empty.elim i
  | some g =>
    cases g with
    | inl c => exact hB.local_probability (v i.val)
    | inr p => exact control_activation_probability μ B q hB p.1.val i.val

/-- Local parity and positive residue independence are used only within each
group, for the actual deterministic path populations. -/
theorem control_route_group_independent {Ω : Type*} [MeasurableSpace Ω] {nv : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (v : Fin nv → BlockSite) (hv : RouteParitySeparated v)
    (N : ℕ) (g : MarkGroup N) :
    iIndepFun (fun i : RouteGroupIndex v N g => markIndicator (routeGroupEvent B v N g i)) μ := by
  cases g with
  | none => exact iIndepFun.of_subsingleton
  | some g =>
    cases g with
    | inl c =>
      apply hB.local_independent (fun i : localRouteGroup nv c => v i.val)
      intro i j hij
      exact hv i.val j.val (fun he => hij (Subtype.ext he)) (local_route_group_parity c i j)
    | inr p =>
      apply hB.positive_independent p.1.val (fun i : positiveRouteGroup v p.1.val p.2 => i.val) p.2
      · exact Subtype.val_injective
      · intro i
        exact (Finset.mem_filter.mp i.property).2

end ASDExplicitGamma.Inverse
