module

public import ASDExplicitGamma.Numerics.GeneratorEigenvalue
public import ASDExplicitGamma.Numerics.AllOrder.CirReadable

/-! The forced-source feedback H+sqrt(H) and explicit
transport coefficients on 0≤rho≤1/243. The half-gain constant
belongs only to NU-MA-LOCAL-CAPS. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics

noncomputable def generatorH : ℝ := 2.265
noncomputable def generatorFeedback : ℝ := generatorH+Real.sqrt generatorH
noncomputable def generatorKA (rho : ℝ) : ℝ :=
  1.860+2.36412*rho*Real.sqrt (156/5)+0.52288*rho^2*Real.sqrt (46488/25)
noncomputable def generatorKB (rho : ℝ) : ℝ :=
  1.860+2.36412*rho*Real.sqrt (78/5)+0.52288*rho^2*Real.sqrt (23244/25)
noncomputable def generatorMuStar (rho : ℝ) : ℝ :=
  generatorLambdaMax (generatorH*(generatorKA rho)^2)
    (generatorFeedback*generatorKA rho*generatorKB rho)

theorem generator_feedback_caps : 0 < generatorFeedback ∧ generatorFeedback < 3.771 := by
  have hs := AllOrder.cir_radical_caps.2.2.2.2.1
  unfold generatorFeedback generatorH
  constructor
  · positivity
  · linarith only [hs]

/-- All transport caps follow from the explicit formulas and source ratio interval. -/
theorem generator_coefficient_caps (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho ≤ 1/243) :
    0 < generatorKA rho ∧ generatorKA rho < 1.915 ∧
      0 < generatorKB rho ∧ generatorKB rho < 1.899 ∧ (generatorKB rho)^2 < 4 := by
  have h := AllOrder.cir_source_coefficients rho hr0 hr
  have ha : 0 < generatorKA rho := by unfold generatorKA; positivity
  have hb : 0 < generatorKB rho := by unfold generatorKB; positivity
  exact ⟨ha,h.1,hb,h.2.1,h.2.2.1⟩

/-- The positive principal minors of L I-A bound the larger characteristic root. -/
theorem generator_lambdaMax_lt_of_principal_minors (a b L : ℝ)
    (hL : 0 < L) (ha : a < L) (hdet : b^2 < L*(L-a)) :
    generatorLambdaMax a b < L := by
  have hpos : 0 < 2*L-a := by linarith only [hL,ha]
  have hs : Real.sqrt (a^2+4*b^2) < 2*L-a := by
    apply (Real.sqrt_lt' hpos).mpr
    nlinarith only [hdet]
  unfold generatorLambdaMax
  linarith only [hs]

/-- An actual eigenvalue dominating all real eigenvalues, for every source ratio. -/
theorem generator_mu_star_is_largest (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho ≤ 1/243) :
    IsLargestRealEigenvalue
      (generatorMatrix (generatorH*(generatorKA rho)^2)
        (generatorFeedback*generatorKA rho*generatorKB rho)) (generatorMuStar rho) := by
  have h := generator_coefficient_caps rho hr0 hr
  exact generator_lambdaMax_is_largest _ _ (mul_pos (mul_pos generator_feedback_caps.1 h.1) h.2.2.1)

/-- The bound on μ* with only the geometric-ratio hypotheses. -/
theorem generator_mu_star_lt (rho : ℝ) (hr0 : 0 ≤ rho) (hr : rho ≤ 1/243) :
    generatorMuStar rho < 19 ∧ (generatorKB rho)^2 < 4 := by
  obtain ⟨ha,hA,hb,hB,hBsq⟩ := generator_coefficient_caps rho hr0 hr
  have hAsq : (generatorKA rho)^2 ≤ (1.915:ℝ)^2 := pow_le_pow_left₀ ha.le hA.le 2
  have hBsq' : (generatorKB rho)^2 ≤ (1.899:ℝ)^2 := pow_le_pow_left₀ hb.le hB.le 2
  have hDsq : generatorFeedback^2 ≤ (3.771:ℝ)^2 :=
    pow_le_pow_left₀ generator_feedback_caps.1.le generator_feedback_caps.2.le 2
  have hdiag : generatorH*(generatorKA rho)^2 ≤ (2.265:ℝ)*1.915^2 :=
    mul_le_mul_of_nonneg_left hAsq (by norm_num [generatorH])
  have hprod : (generatorFeedback*generatorKA rho*generatorKB rho)^2 ≤
      (3.771:ℝ)^2*1.915^2*1.899^2 := by
    simp only [mul_pow]
    exact mul_le_mul (mul_le_mul hDsq hAsq (sq_nonneg _) (by positivity))
      hBsq' (sq_nonneg _) (by positivity)
  have hminor : (0:ℝ) < 19-2.265*1.915^2 := by
    convert (Rat.cast_lt (K := ℝ)).mpr AllOrder.cir_principal_minors.2.2.1 using 1 <;> norm_num
  have hdet : (15:ℝ) < 19*(19-2.265*1.915^2)-3.771^2*1.915^2*1.899^2 := by
    convert (Rat.cast_lt (K := ℝ)).mpr AllOrder.cir_principal_minors.2.2.2.1 using 1 <;> norm_num
  refine ⟨generator_lambdaMax_lt_of_principal_minors _ _ 19 (by norm_num) ?_ ?_,hBsq⟩
  · linarith only [hdiag,hminor]
  · nlinarith only [hdiag,hprod,hdet]

end ASDExplicitGamma.Numerics
