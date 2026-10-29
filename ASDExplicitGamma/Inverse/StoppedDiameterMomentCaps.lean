module

public import ASDExplicitGamma.Inverse.StoppedDiameterRareMoments
public import ASDExplicitGamma.Inverse.StoppedRareMomentCertificates

/-! The actual planar fourth and eighth moments required by weighted Bernstein. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- Uniform planar rare moments M4<8 and M8<10^9, derived from the actual
source field. No moment premise is passed to this theorem. -/
theorem real_diameter_uniform_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) :
    Integrable (fun ω => (realDiameterField B x ω)^4) μ ∧
    Integrable (fun ω => (realDiameterField B x ω)^8) μ ∧
      (∫ ω, (realDiameterField B x ω)^4 ∂μ) < 8 ∧
      (∫ ω, (realDiameterField B x ω)^8 ∂μ) < 1000000000 := by
  have hm := real_diameter_measurable B hB.local_measurable hB.positive_measurable x
  have hrare (u : ℝ) (hu : 0 < u) : μ.real {ω | u < realDiameterField B x ω} ≤ (26/10000000000:ℝ) := by
    have hh := (real_diameter_tail μ B q hB hq0 hq hfloor x u hu.le).trans (min_le_left _ _)
    have hq' := mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 26)
    linarith only [hh,hq']
  have hexp (u : ℝ) (hu : 0 < u) : μ.real {ω | u < realDiameterField B x ω} ≤ 200*Real.exp (-u/4) :=
    (real_diameter_tail μ B q hB hq0 hq hfloor x u hu.le).trans (min_le_right _ _)
  have h4 := nat_moment_of_two_tails μ _ hm (fun _ => ENNReal.toReal_nonneg) 3
    (26/10000000000) 200 104 (by norm_num) (by norm_num) (by norm_num)
    uniform_rare_moment_cutoff hrare hexp
  have h8 := nat_moment_of_two_tails μ _ hm (fun _ => ENNReal.toReal_nonneg) 7
    (26/10000000000) 200 104 (by norm_num) (by norm_num) (by norm_num)
    uniform_rare_moment_cutoff hrare hexp
  exact ⟨h4.1,h8.1,h4.2.trans_lt uniform_rare_moment_caps.1,h8.2.trans_lt uniform_rare_moment_caps.2⟩

end
end ASDExplicitGamma.Inverse
