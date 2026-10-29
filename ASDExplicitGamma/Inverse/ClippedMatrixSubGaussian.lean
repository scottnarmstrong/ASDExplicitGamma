module

public import ASDExplicitGamma.Inverse.WeightedLocalizationLp
public import Mathlib.Probability.Moments.SubGaussian

/-! Real-order sub-Gaussian norms for the centered clipped-matrix entries. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A finite sub-Gaussian variance proxy gives a real-order extended norm.
This keeps the source exponent, with no ceiling or integer rounding. -/
theorem clipped_subGaussian_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ≥0) (hX : HasSubgaussianMGF X c μ)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm X (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2*Real.sqrt p*Real.sqrt (c:ℝ)) := by
  by_cases hc : c=0
  · subst c
    rw [eLpNorm_congr_ae hX.ae_eq_zero_of_hasSubgaussianMGF_zero]
    simp only [eLpNorm_zero,NNReal.coe_zero,Real.sqrt_zero,mul_zero,ENNReal.ofReal_zero,le_refl]
  have hc0 : 0 < (c:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let r := Real.sqrt (c:ℝ)
  let z := Real.sqrt p
  let lam := z/r
  have hr : 0 < r := Real.sqrt_pos.mpr hc0
  have hz : 0 < z := Real.sqrt_pos.mpr hp0
  have hrs : r^2=(c:ℝ) := Real.sq_sqrt hc0.le
  have hzs : z^2=p := Real.sq_sqrt hp0.le
  have ht (s : ℝ) (hs : s=lam ∨ s= -lam) : (c:ℝ)*s^2/2 ≤ p := by
    rcases hs with rfl | rfl <;>
      dsimp only [lam] <;> rw [← hrs,← hzs] <;> field_simp <;> nlinarith only [sq_nonneg z]
  have hh := localization_eLpNorm_of_exp_bounds μ X hX.aemeasurable p lam hp
    (div_pos hz hr) (hX.integrable_exp_mul lam) (hX.integrable_exp_mul (-lam))
    ((hX.mgf_le lam).trans (Real.exp_le_exp.mpr (ht _ (Or.inl rfl))))
    ((hX.mgf_le (-lam)).trans (Real.exp_le_exp.mpr (ht _ (Or.inr rfl))))
  apply hh.trans_eq
  congr 1
  change 2*(p/(z/r))=2*z*r
  rw [← hzs]
  field_simp

end ASDExplicitGamma.Inverse
