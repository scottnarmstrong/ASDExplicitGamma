module

public import Homogenization.Probability.IndependentSums.Rosenthal.ScalarBennett

/-! The variance-sensitive small-tilt MGF used in weighted planar localization. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization.IndependentSums MeasureTheory ProbabilityTheory

/-- On the unit interval the exponential remainder is bounded by the square. -/
theorem localization_exp_remainder_le_sq {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 - x ≤ x ^ 2 := by
  have hh := Real.norm_exp_sub_one_sub_id_le (x := x) (by simpa only [Real.norm_of_nonneg hx] using hx1)
  rw [Real.norm_of_nonneg hx] at hh
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)

/-- Independent centered bounded summands have a variance-sensitive Gaussian
MGF bound throughout the small-tilt window. -/
theorem localization_sum_mgf_le {Ω ι : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (X : ι → Ω → ℝ) (s : Finset ι)
    (hind : iIndepFun X mu) (hm : ∀ i, Measurable (X i))
    (b V lam : ℝ) (hb : 0 < b) (hlam : 0 ≤ lam) (htilt : lam * b ≤ 1)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂mu, |X i ω| ≤ b)
    (hmean : ∀ i ∈ s, ∫ ω, X i ω ∂mu = 0)
    (hV : (∑ i ∈ s, moment (X i) 2 mu) ≤ V) :
    mgf (fun ω => ∑ i ∈ s, X i ω) mu lam ≤ Real.exp (lam ^ 2 * V) := by
  have hh := mgf_finset_sum_le_bennett_of_iIndepFun_of_abs_le_of_integral_eq_zero
    hind hm hb hlam hbound hmean
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hvar : 0 ≤ ∑ i ∈ s, moment (X i) 2 mu := by
    apply Finset.sum_nonneg
    intro i _
    exact integral_nonneg (fun ω => sq_nonneg (X i ω))
  have he := localization_exp_remainder_le_sq (mul_nonneg hlam hb.le) htilt
  calc
    _ ≤ ((∑ i ∈ s, moment (X i) 2 mu) / b ^ 2) * (lam * b) ^ 2 :=
      mul_le_mul_of_nonneg_left he (div_nonneg hvar (sq_nonneg b))
    _ = lam ^ 2 * (∑ i ∈ s, moment (X i) 2 mu) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hV (sq_nonneg lam)

end ASDExplicitGamma.Inverse
