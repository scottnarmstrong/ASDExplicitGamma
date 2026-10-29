module

public import ASDExplicitGamma.Inverse.StoppedIndependentMarks
public import ASDExplicitGamma.Inverse.StoppedCorrelatedGroups
public import Mathlib.Probability.Moments.Basic

/-! Marked-path charge bounds with independence only inside the specified finite groups. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

/-- Each independent group pays the common per-path budget from its own
Bernoulli probability and tilt, including empty mark populations. -/
theorem mark_group_mgf_budget {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : I → Set Ω) (hE : ∀ i, MeasurableSet (E i))
    (hind : iIndepFun (fun i => markIndicator (E i)) μ)
    (q t n : ℝ) (ht : 0 ≤ t) (hq : ∀ i, μ.real (E i) ≤ q)
    (hcost : q*(Real.exp t-1) ≤ 1/10) (hcard : (Fintype.card I:ℝ) ≤ n) :
    (∫ ω, Real.exp (t*∑ i, markIndicator (E i) ω) ∂μ) ≤ Real.exp (n/10) := by
  apply (independent_marks_mgf μ E hE hind q t ht hq).trans
  apply Real.exp_le_exp.mpr
  calc
    _ = (Fintype.card I:ℝ)*(q*(Real.exp t-1)) := by ring
    _ ≤ (Fintype.card I:ℝ)*(1/10) := mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg _)
    _ ≤ n*(1/10) := mul_le_mul_of_nonneg_right hcard (by norm_num)
    _ = _ := by ring

/-- The finite charge is the actual sum of the group mark indicators with
physical side weights. No independence between groups is required. -/
theorem marked_charge_mgf {Ω G : Type*} [MeasurableSpace Ω] [Fintype G]
    (I : G → Type*) [∀ g, Fintype (I g)] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : (g : G) → I g → Set Ω) (hE : ∀ g i, MeasurableSet (E g i))
    (hind : ∀ g, iIndepFun (fun i => markIndicator (E g i)) μ)
    (w c q : G → ℝ) (hw : ∀ g, 0 < w g) (hwsum : ∑ g, w g = 1)
    (hc : ∀ g, 0 ≤ c g) (n : ℝ)
    (hq : ∀ g i, μ.real (E g i) ≤ q g)
    (hcost : ∀ g, q g*(Real.exp (5*c g/w g)-1) ≤ 1/10)
    (hcard : ∀ g, (Fintype.card (I g):ℝ) ≤ n) :
    Integrable (fun ω => Real.exp (5*∑ g, c g*∑ i, markIndicator (E g i) ω)) μ ∧
    (∫ ω, Real.exp (5*∑ g, c g*∑ i, markIndicator (E g i) ω) ∂μ) ≤ Real.exp (n/10) := by
  let Y (g : G) (ω : Ω) := (5*c g/w g)*∑ i, markIndicator (E g i) ω
  have hY (g : G) : Measurable (Y g) := measurable_const.mul
    (Finset.measurable_sum Finset.univ (fun i _ => mark_indicator_measurable (E g i) (hE g i)))
  have ht (g : G) : 0 ≤ 5*c g/w g := div_nonneg (mul_nonneg (by norm_num) (hc g)) (hw g).le
  have hInt (g : G) : Integrable (fun ω => Real.exp (Y g ω)) μ :=
    mark_sum_exp_integrable μ (E g) (hE g) _ (ht g)
  have hbound (g : G) : (∫ ω, Real.exp (Y g ω) ∂μ) ≤ Real.exp (n/10) :=
    mark_group_mgf_budget μ (E g) (hE g) (hind g) (q g) _ n (ht g) (hq g) (hcost g) (hcard g)
  have hh := correlated_groups_exp_bound μ w (fun g => (hw g).le) hwsum Y hY hInt _ hbound
  have he (ω : Ω) : (∑ g, w g*Y g ω) = 5*∑ g, c g*∑ i, markIndicator (E g i) ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    dsimp only [Y]
    field_simp [(hw g).ne']
  simpa only [he] using hh

/-- The source marked-path charge has an exponential probability bound before
the finite path count, with all cross-label dependence still allowed. -/
theorem marked_charge_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (n : ℝ)
    (hInt : Integrable (fun ω => Real.exp (5*X ω)) μ)
    (hMgf : (∫ ω, Real.exp (5*X ω) ∂μ) ≤ Real.exp (n/10)) :
    μ.real {ω | n ≤ X ω} ≤ Real.exp (-(49/10:ℝ)*n) := by
  have hh := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) n (by norm_num : (0:ℝ) ≤ 5) hInt
  apply hh.trans
  calc
    _ ≤ Real.exp (-5*n)*Real.exp (n/10) := mul_le_mul_of_nonneg_left hMgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end ASDExplicitGamma.Inverse
