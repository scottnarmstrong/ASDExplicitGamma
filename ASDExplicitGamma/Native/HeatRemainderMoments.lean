module

public import ASDExplicitGamma.Native.HeatRemainderJAlgebra
public import ASDExplicitGamma.Native.GenericSourceMeanHolder

/-! Finite, correlated VHEAT moments on the actual joint probability space. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A prime L1 cap proves integrability before the real expectation is taken. -/
theorem heat_remainder_integral_of_prime_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω,0 ≤ f ω)
    (A : ℝ) (hA : 0 ≤ A) (hcap : eLpNorm' f 1 μ ≤ ENNReal.ofReal A) :
    Integrable f μ ∧ (∫ ω,f ω ∂μ) ≤ A := by
  have he : eLpNorm f 1 μ = eLpNorm' f 1 μ := by
    simpa using eLpNorm_eq_eLpNorm' (p := (1:ℝ≥0∞)) (by norm_num) (by norm_num) hf
  have hm : MemLp f 1 μ := memLp_iff.mpr ((he.le.trans hcap).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨memLp_one_iff_integrable.mp hm, ?_⟩
  have hc : (∫⁻ ω,ENNReal.ofReal (f ω) ∂μ) ≤ ENNReal.ofReal A := by
    simpa only [eLpNorm'_eq_lintegral_enorm,one_div_one,ENNReal.rpow_one,
      Real.enorm_eq_ofReal (hf0 _)] using hcap
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc).trans_eq (ENNReal.toReal_ofReal hA)

/-- The complete rare monomial bill, with finiteness included in the export. -/
theorem heat_remainder_rare_moment_le_J
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (j : Fin 2) (l : ℕ) (hl : l ≤ 20)
    (e X F : ℝ) (he : 0 ≤ e) (hX : 0 < X) (hF : 0 ≤ F)
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal e)
    (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal X)
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal F) :
    Integrable (fun ω => R ω^(j.val+1)*T ω^l) μ ∧
      (∫ ω,R ω^(j.val+1)*T ω^l ∂μ) ≤ nativeHeatVHEATJ e X F 20 (j.val+1) l := by
  exact heat_remainder_integral_of_prime_cap μ _ ((hR.pow _).mul (hT.pow _))
    (fun ω => mul_nonneg (pow_nonneg (hR0 ω) _) (pow_nonneg (hT0 ω) _)) _
    (nativeHeatVHEATJ_nonneg _ _ _ _ _ _ he hX hF)
    (heat_remainder_rare_monomial_le_J μ R T hR hT hR0 hT0 j l hl e X F he hX hF hRc h20 h128)

end
end ASDExplicitGamma.Native
