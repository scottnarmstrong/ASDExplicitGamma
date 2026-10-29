module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! Complete-mode joint Cauchy budget for the OLD mixed trial errors. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Square-summable nonnegative local norms give genuine summability and
the constant-one bound for a signed mixed-mode pairing. -/
theorem old_signed_series_pairing_budget {I : Type*} (a b f : I → ℝ)
    (ha : ∀ n,0≤a n) (hb : ∀ n,0≤b n)
    (has : Summable (fun n => a n^2)) (hbs : Summable (fun n => b n^2))
    (hbound : ∀ n,|f n|≤a n*b n) :
    Summable f ∧ |∑' n,f n|≤Real.sqrt (∑' n,a n^2)*Real.sqrt (∑' n,b n^2) := by
  have hab : Summable (fun n => a n*b n) := (has.add hbs).of_nonneg_of_le
    (fun n => mul_nonneg (ha n) (hb n)) (fun n => by nlinarith only [sq_nonneg (a n-b n)])
  have habs : Summable (fun n => |f n|) := hab.of_nonneg_of_le (fun n => abs_nonneg _) hbound
  have hf : Summable f := Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have hc : (∑' n,a n*b n)≤Real.sqrt (∑' n,a n^2)*Real.sqrt (∑' n,b n^2) := by
    apply Real.tsum_le_of_sum_le (fun n => mul_nonneg (ha n) (hb n))
    intro s
    have hh := Real.sum_sqrt_mul_sqrt_le s (fun n => sq_nonneg (a n)) (fun n => sq_nonneg (b n))
    simp_rw [Real.sqrt_sq (ha _),Real.sqrt_sq (hb _)] at hh
    exact hh.trans (mul_le_mul
      (Real.sqrt_le_sqrt (has.sum_le_tsum s (fun n _ => sq_nonneg _)))
      (Real.sqrt_le_sqrt (hbs.sum_le_tsum s (fun n _ => sq_nonneg _)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine ⟨hf,?_⟩
  have hn := norm_tsum_le_tsum_norm (f := f) habs
  simp only [Real.norm_eq_abs] at hn
  exact hn.trans ((habs.tsum_le_tsum hbound hab).trans hc)

end
end ASDExplicitGamma.Native
