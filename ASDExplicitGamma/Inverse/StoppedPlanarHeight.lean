module

public import ASDExplicitGamma.Inverse.StoppedSeparationEvents
public import ASDExplicitGamma.Inverse.StoppedMarkedMeasurable
public import ASDExplicitGamma.Inverse.StoppedHeightGood

/-! Actual marked planar stopped heights from the named probability and restriction inputs. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- The source selected height for the actual scale-indexed marked fields and
root-relative finite starting populations. -/
def planarStoppedHeight {Ω : Type*} (H0 : ℕ) (B : ℕ → PlanarMarks Ω)
    (x : (h : ℕ) → RootStartingIndex h → BlockSite) : Ω → ℕ :=
  stoppedHeight H0 (fun h => separationFailure (B h) h (x h))

/-- The actual full separation event is measurable, including the connected
occupied component and every positive label. -/
theorem separation_failure_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x))
    (h : ℕ) (x : RootStartingIndex h → BlockSite) :
    MeasurableSet (separationFailure B h x) :=
  MeasurableSet.iUnion (fun i => cluster_reaches_measurable B hL hP (x i) _)

/-- The exact source height is an ordinary measurable random variable. -/
theorem planar_stopped_height_measurable {Ω : Type*} [MeasurableSpace Ω]
    (H0 : ℕ) (B : ℕ → PlanarMarks Ω)
    (hL : ∀ h x, MeasurableSet ((B h).localMark x))
    (hP : ∀ h n x, MeasurableSet ((B h).positiveMark n x))
    (x : (h : ℕ) → RootStartingIndex h → BlockSite) :
    Measurable (planarStoppedHeight H0 B x) :=
  stopped_height_measurable H0 _ (fun h => separation_failure_measurable (B h) (hL h) (hP h) h (x h))

/-- The fixed source entrance is retained samplewise. -/
theorem planar_stopped_height_ge {Ω : Type*} (H0 : ℕ) (B : ℕ → PlanarMarks Ω)
    (x : (h : ℕ) → RootStartingIndex h → BlockSite) (ω : Ω) :
    H0 ≤ planarStoppedHeight H0 B x ω := stopped_height_ge H0 _ ω

/-- The exact exp(-3^(h/4-40)/32) stopped-height tail, for either source
entrance, with actual infinite marked fields and the full root population. -/
theorem planar_stopped_height_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H0 : ℕ) (hH0 : 333 ≤ H0)
    (B : ℕ → PlanarMarks Ω) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hB : ∀ h, H0 ≤ h → PlanarMarkControl μ (B h) q)
    (x : (h : ℕ) → RootStartingIndex h → BlockSite) (h : ℕ) (hh : H0 ≤ h) :
    μ.real {ω | h < planarStoppedHeight H0 B x ω} ≤ Real.exp (-heightExponent h/32) :=
  stopped_height_tail μ H0 hH0 _
    (fun k hk => separation_failure_probability μ (B k) q (hB k hk) hq0 hq k (hH0.trans hk) (x k)) h hh

/-- Almost surely every separation at and above the selected source height
succeeds. This is the actual property consumed by stopped-chain geometry. -/
theorem planar_stopped_height_ae_good {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H0 : ℕ) (hH0 : 333 ≤ H0)
    (B : ℕ → PlanarMarks Ω) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hB : ∀ h, H0 ≤ h → PlanarMarkControl μ (B h) q)
    (x : (h : ℕ) → RootStartingIndex h → BlockSite) :
    ∀ᵐ ω ∂μ, ∀ h, planarStoppedHeight H0 B x ω ≤ h → ω ∉ separationFailure (B h) h (x h) := by
  have hh := stopped_height_ae_good μ H0 hH0 (fun h => separationFailure (B h) h (x h))
    (fun k hk => separation_failure_probability μ (B k) q (hB k hk) hq0 hq k (hH0.trans hk) (x k))
  filter_upwards [hh] with ω hω
  exact hω.2

end
end ASDExplicitGamma.Inverse
