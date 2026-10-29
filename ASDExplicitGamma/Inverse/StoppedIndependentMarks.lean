module

public import ASDExplicitGamma.Inverse.StoppedBernoulliMGF

/-! Independent subfamily MGFs, without any assumption of independence across labels. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- Literal marks lie in the unit interval at every sample. -/
theorem mark_indicator_bounds {Ω : Type*} (E : Set Ω) (ω : Ω) :
    0 ≤ markIndicator E ω ∧ markIndicator E ω ≤ 1 := by
  classical
  by_cases h : ω ∈ E <;> simp [markIndicator,h]

/-- Every finite mark-sum exponential is integrable, even before using
independence; the deterministic finite population provides its bound. -/
theorem mark_sum_exp_integrable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => Real.exp (t*∑ i, markIndicator (E i) ω)) μ := by
  have hm : Measurable (fun ω => Real.exp (t*∑ i, markIndicator (E i) ω)) :=
    (measurable_const.mul (Finset.measurable_sum Finset.univ (fun i _ => mark_indicator_measurable (E i) (hE i)))).exp
  apply Integrable.mono' (integrable_const (Real.exp (t*(Fintype.card I:ℝ)))) hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ht
  calc
    _ ≤ ∑ _i : I, (1:ℝ) := Finset.sum_le_sum fun i _ => (mark_indicator_bounds (E i) ω).2
    _ = _ := by simp

/-- A finite independent mark family pays only its exact number of potential
marks and their probability cap, at the full supplied tilt. -/
theorem independent_marks_mgf {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hind : iIndepFun (fun i => markIndicator (E i)) μ)
    (q t : ℝ) (ht : 0 ≤ t) (hq : ∀ i, μ.real (E i) ≤ q) :
    (∫ ω, Real.exp (t*∑ i, markIndicator (E i) ω) ∂μ) ≤
      Real.exp ((Fintype.card I:ℝ)*q*(Real.exp t-1)) := by
  have hi := hind.comp (fun (_ : I) (x : ℝ) => Real.exp (t*x))
    (fun _ => (measurable_const.mul measurable_id).exp)
  have hm (i : I) : AEStronglyMeasurable (fun ω => Real.exp (t*markIndicator (E i) ω)) μ :=
    ((measurable_const.mul (mark_indicator_measurable (E i) (hE i))).exp).aestronglyMeasurable
  have hprod := hi.integral_fun_prod_eq_prod_integral hm
  simp only [Function.comp_def] at hprod
  have he : (fun ω => Real.exp (t*∑ i, markIndicator (E i) ω)) =
      (fun ω => ∏ i, Real.exp (t*markIndicator (E i) ω)) := by
    funext ω
    rw [Finset.mul_sum,Real.exp_sum]
  rw [he,hprod]
  calc
    _ ≤ ∏ _i : I, Real.exp (q*(Real.exp t-1)) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact integral_nonneg (fun _ => (Real.exp_pos _).le)
      · intro i _
        exact mark_mgf_le μ (E i) (hE i) q t ht (hq i)
    _ = _ := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end
end ASDExplicitGamma.Inverse
