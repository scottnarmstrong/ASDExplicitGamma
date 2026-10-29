module

public import ASDExplicitGamma.Native.GenericSourceHolderProducts
public import ASDExplicitGamma.Gaussian.GaussMomentHolder

/-! The rare mean costs, with actual finite probability-space seminorms. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- A finite prime cap controls the real nonnegative norm at any positive
finite exponent. Finiteness is established before taking toReal. -/
theorem native_source_positive_norm_le_prime_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (p A : ℝ) (hp : 0 < p) (hA : 0 ≤ A)
    (hcap : eLpNorm' f p μ ≤ ENNReal.ofReal A) : positiveLpNorm μ p f ≤ A := by
  have he : eLpNorm f (ENNReal.ofReal p) μ = eLpNorm' f p μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      eLpNorm_eq_eLpNorm' (p := ENNReal.ofReal p) (by exact ne_of_gt (ENNReal.ofReal_pos.mpr hp))
        ENNReal.ofReal_ne_top hf
  have hc := he.le.trans hcap
  have hmem : MemLp f (ENNReal.ofReal p) μ := memLp_iff.mpr (hc.trans_lt ENNReal.ofReal_lt_top)
  rw [positiveLpNorm_eq_eLpNorm_toReal μ hp f hf0 hmem]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc).trans_eq (ENNReal.toReal_ofReal hA)

/-- Cauchy bounds a rare positive product by the two separately finite caps. -/
theorem native_source_integral_product_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (R F : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hF : AEStronglyMeasurable F μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hF0 : ∀ ω, 0 ≤ F ω)
    (e u : ℝ) (he : 0 ≤ e) (hu : 0 ≤ u)
    (hRc : eLpNorm' R 2 μ ≤ ENNReal.ofReal e)
    (hFc : eLpNorm' F 2 μ ≤ ENNReal.ofReal u) :
    Integrable (fun ω => R ω*F ω) μ ∧ (∫ ω, R ω*F ω ∂μ) ≤ e*u := by
  have hRm : MemLp R (ENNReal.ofReal 2) μ := by
    apply memLp_iff.mpr
    rw [eLpNorm_eq_eLpNorm' (by norm_num : ENNReal.ofReal (2:ℝ)≠0) ENNReal.ofReal_ne_top hR]
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤2)] using hRc.trans_lt ENNReal.ofReal_lt_top
  have hFm : MemLp F (ENNReal.ofReal 2) μ := by
    apply memLp_iff.mpr
    rw [eLpNorm_eq_eLpNorm' (by norm_num : ENNReal.ofReal (2:ℝ)≠0) ENNReal.ofReal_ne_top hF]
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤2)] using hFc.trans_lt ENNReal.ofReal_lt_top
  have hc : (2:ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr (by norm_num)
  have sourceMeanHolderTriple : ENNReal.HolderTriple (ENNReal.ofReal (2:ℝ)) (ENNReal.ofReal (2:ℝ)) 1 := hc.ennrealOfReal
  refine ⟨hRm.integrable_mul hFm,?_⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hc (Filter.Eventually.of_forall hR0)
    (Filter.Eventually.of_forall hF0) hRm hFm
  have hh' : (∫ ω, R ω*F ω ∂μ) ≤ positiveLpNorm μ 2 R*positiveLpNorm μ 2 F := by
    simpa only [positiveLpNorm,one_div] using hh
  exact hh'.trans (mul_le_mul
    (native_source_positive_norm_le_prime_cap μ R hR hR0 2 e (by norm_num) he hRc)
    (native_source_positive_norm_le_prime_cap μ F hF hF0 2 u (by norm_num) hu hFc)
    (Real.rpow_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (hF0 _) _)) _)
    he)

/-- The genuine rare bank reserve pays all four mean moments. Its square
uses L64 before inclusion in L2; no independence is assumed. -/
theorem native_source_rare_mean_moments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (e x : ℝ) (he : 0 ≤ e) (hx : 0 ≤ x)
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal e)
    (hTc : eLpNorm' T 20 μ ≤ ENNReal.ofReal x) :
    (Integrable R μ ∧ (∫ ω, R ω ∂μ) ≤ e) ∧
    (Integrable (fun ω => R ω*T ω) μ ∧ (∫ ω, R ω*T ω ∂μ) ≤ e*x) ∧
    (Integrable (fun ω => (R ω)^2) μ ∧ (∫ ω, (R ω)^2 ∂μ) ≤ e^2) ∧
    (Integrable (fun ω => (R ω)^2*T ω) μ ∧ (∫ ω, (R ω)^2*T ω ∂μ) ≤ e^2*x) := by
  have hR2 : eLpNorm' R 2 μ ≤ ENNReal.ofReal e :=
    (eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) (by norm_num) μ hR).trans hRc
  have hT2 : eLpNorm' T 2 μ ≤ ENNReal.ofReal x :=
    (eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) (by norm_num) μ hT).trans hTc
  have hsq64 := native_source_holder_inverse_square μ R hR (ENNReal.ofReal e) hRc
  have hsq2 : eLpNorm' (fun ω => (R ω)^2) 2 μ ≤ ENNReal.ofReal (e^2) := by
    exact (eLpNorm'_le_eLpNorm'_of_exponent_le (by norm_num) (by norm_num) μ (hR.pow 2)).trans
      (hsq64.trans_eq (by rw [ENNReal.ofReal_pow he]))
  have hone : eLpNorm' (fun _ : Ω => (1:ℝ)) 2 μ ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm'_const_of_isProbabilityMeasure 1 (by norm_num),Real.enorm_eq_ofReal (by norm_num)]
  have h1 := native_source_integral_product_le μ R (fun _ => 1) hR aestronglyMeasurable_const
    hR0 (fun _ => by norm_num) e 1 he (by norm_num) hR2 hone
  have h2 := native_source_integral_product_le μ R T hR hT hR0 hT0 e x he hx hR2 hT2
  have h3 := native_source_integral_product_le μ (fun ω => (R ω)^2) (fun _ => 1)
    (hR.pow 2) aestronglyMeasurable_const (fun _ => sq_nonneg _) (fun _ => by norm_num)
    (e^2) 1 (sq_nonneg e) (by norm_num) hsq2 hone
  have h4 := native_source_integral_product_le μ (fun ω => (R ω)^2) T
    (hR.pow 2) hT (fun _ => sq_nonneg _) hT0 (e^2) x (sq_nonneg e) hx hsq2 hT2
  exact ⟨by simpa only [mul_one] using h1,h2,by simpa only [mul_one] using h3,h4⟩

end
end ASDExplicitGamma.Native
