module

public import ASDExplicitGamma.Inverse.StoppedRealDiameter
public import ASDExplicitGamma.Inverse.StoppedRareMomentBound

/-! The actual diameter moments with the exact source rare-moment polynomial. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- Every positive integer source moment, including M2,M4,M8, follows from
the literal diameter tail at any admissible source cutoff T. -/
theorem real_diameter_nat_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hcut : 200*Real.exp (-T/4) ≤ 26*q) :
    Integrable (fun ω => (realDiameterField B x ω)^(n+1)) μ ∧
      (∫ ω, (realDiameterField B x ω)^(n+1) ∂μ) ≤
        (26*q)*rareMomentPolynomial (n+1) T := by
  apply nat_moment_of_two_tails μ _
    (real_diameter_measurable B hB.local_measurable hB.positive_measurable x)
    (fun _ => ENNReal.toReal_nonneg) n (26*q) 200 T (by positivity) (by norm_num) hT hcut
  · intro u hu
    exact (real_diameter_tail μ B q hB hq0 hq hfloor x u hu.le).trans (min_le_left _ _)
  · intro u hu
    exact (real_diameter_tail μ B q hB hq0 hq hfloor x u hu.le).trans (min_le_right _ _)

end
end ASDExplicitGamma.Inverse
