module

public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import Mathlib.MeasureTheory.Measure.Prod

/-! Measurable passage from a jointly measurable spatial field to its L²
class. This is used for the correlated full band load in the cell trial. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory TopologicalSpace
noncomputable section

/-- Distance tests suffice for measurability into a second-countable metric
space. The ball basis is used without choosing representatives. -/
theorem upper_cell_measurable_of_dist
    {Ω H : Type*} [MeasurableSpace Ω] [MetricSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (F : Ω → H) (hF : ∀ y, Measurable (fun ω => dist (F ω) y)) : Measurable F := by
  have hb : IsTopologicalBasis {s : Set H | ∃ y r, s = Metric.ball y r} := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro s ⟨y,r,rfl⟩
      exact Metric.isOpen_ball
    · intro x s hx hs
      obtain ⟨r,hr,hrs⟩ := Metric.isOpen_iff.mp hs x hx
      exact ⟨Metric.ball x r, ⟨x,r,rfl⟩, Metric.mem_ball_self hr, hrs⟩
  rw [‹BorelSpace H›.measurable_eq, hb.borel_eq_generateFrom]
  apply measurable_generateFrom
  rintro s ⟨y,r,rfl⟩
  exact measurableSet_lt (hF y) measurable_const

/-- With all spatial sections in L², joint measurability gives measurability
of the L²-valued section map. -/
theorem upper_cell_toLp_measurable
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure X) [SFinite μ]
    [MeasurableSpace (Lp E 2 μ)] [BorelSpace (Lp E 2 μ)]
    [SecondCountableTopology (Lp E 2 μ)]
    (F : Ω → X → E) (hF : Measurable (Function.uncurry F))
    (hmem : ∀ ω, MemLp (F ω) 2 μ) :
    Measurable (fun ω => (hmem ω).toLp (F ω)) := by
  apply upper_cell_measurable_of_dist
  intro g
  have hdiff : Measurable (fun p : Ω × X => F p.1 p.2 - g p.2) :=
    hF.sub ((Lp.stronglyMeasurable g).measurable.comp measurable_snd)
  have hnorm : Measurable (fun ω => eLpNorm (fun x => F ω x - g x) 2 μ) := by
    have hm := (hdiff.enorm.pow_const (2:ℝ)).lintegral_prod_right' (ν := μ)
    have hr := hm.pow_const (1/(2:ℝ))
    convert hr using 1
    funext ω
    simpa only [ENNReal.toReal_ofNat, Pi.sub_def] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal))
        (by norm_num) (by norm_num)
        ((hmem ω).aestronglyMeasurable.sub (Lp.aestronglyMeasurable g)))
  have heq (ω : Ω) : dist ((hmem ω).toLp (F ω)) g =
      (eLpNorm (fun x => F ω x - g x) 2 μ).toReal := by
    rw [Lp.dist_def]
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [(hmem ω).coeFn_toLp] with x hx
    exact congrArg (fun y => y-g x) hx
  simp_rw [heq]
  exact hnorm.ennreal_toReal

end
end ASDExplicitGamma.Scalar
