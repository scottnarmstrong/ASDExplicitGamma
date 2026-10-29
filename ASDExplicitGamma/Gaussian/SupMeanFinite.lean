module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Order.Lattice

/-! Finite mesh maxima in the dyadic-center Gaussian chaining argument. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory

/-- The actual maximum over a nonempty finite family of mesh increments. -/
noncomputable def supMeanFiniteMaximum {ι Ω : Type*} (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) : Ω → ℝ := s.sup' hs X

theorem supMean_finite_max_integrable {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) μ) : Integrable (supMeanFiniteMaximum s hs X) μ := by
  exact Finset.sup'_induction hs X (p := fun f : Ω → ℝ => Integrable f μ)
    (fun _ hf _ hg => Integrable.sup hf hg) hX

/-- The exponential of a finite maximum is bounded by the sum of the
exponentials, without an independence assumption. -/
theorem supMean_exp_finite_max_le {ι Ω : Type*} (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (lam : ℝ) (ω : Ω) :
    Real.exp (lam * supMeanFiniteMaximum s hs X ω) ≤
      ∑ i ∈ s, Real.exp (lam * X i ω) := by
  classical
  have he : supMeanFiniteMaximum s hs X ω = s.sup' hs (fun i => X i ω) := by
    exact Finset.sup'_apply _ _ _
  rw [he]
  obtain ⟨i, hi, heq⟩ := s.exists_mem_eq_sup' hs (fun i => X i ω)
  rw [heq]
  exact Finset.single_le_sum (f := fun j => Real.exp (lam * X j ω))
    (fun j _ => (Real.exp_pos _).le) hi

/-- Jensen and the finite exponential union give the exact log-cardinality
mesh bound at any positive exponential parameter. -/
theorem supMean_finite_max_bound {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (hs : s.Nonempty)
    (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i ∈ s, Integrable (X i) μ) (lam c : ℝ) (hlam : 0 < lam)
    (hE : ∀ i ∈ s, Integrable (fun ω => Real.exp (lam * X i ω)) μ)
    (hmgf : ∀ i ∈ s, (∫ ω, Real.exp (lam * X i ω) ∂μ) ≤ Real.exp c) :
    (∫ ω, supMeanFiniteMaximum s hs X ω ∂μ) ≤ (Real.log s.card + c) / lam := by
  have hM := Finset.measurable_sup' hs (fun i _ => hXm i)
  have hMI := supMean_finite_max_integrable μ s hs X hX
  have hsum := integrable_finsetSum s hE
  have heI : Integrable (fun ω => Real.exp (lam * supMeanFiniteMaximum s hs X ω)) μ := by
    apply hsum.mono' ((hM.const_mul lam).exp.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact supMean_exp_finite_max_le s hs X lam ω
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (hMI.const_mul lam) heI
  rw [integral_const_mul] at hj
  have hb : (∫ ω, Real.exp (lam * supMeanFiniteMaximum s hs X ω) ∂μ) ≤
      (s.card : ℝ) * Real.exp c := by
    calc
      _ ≤ ∫ ω, ∑ i ∈ s, Real.exp (lam * X i ω) ∂μ :=
        integral_mono heI hsum (supMean_exp_finite_max_le s hs X lam)
      _ = ∑ i ∈ s, ∫ ω, Real.exp (lam * X i ω) ∂μ := integral_finsetSum s hE
      _ ≤ ∑ _i ∈ s, Real.exp c := Finset.sum_le_sum hmgf
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hn : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [← Real.exp_log hn, ← Real.exp_add] at hb
  exact (le_div_iff₀ hlam).mpr (by
    have h := Real.exp_le_exp.mp (hj.trans hb)
    linarith only [h])

/-- The optimal finite Gaussian mesh payment is L*sqrt(2 log card).
The centered exponential estimate is a structural input to this generic
maximum lemma, to be supplied by Gaussian concentration at its applications. -/
theorem supMean_finite_max_subgaussian {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset ι) (hs : s.Nonempty)
    (hcard : 2 ≤ s.card) (X : ι → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i ∈ s, Integrable (X i) μ) (m L : ℝ) (hL : 0 < L)
    (hE : ∀ lam > 0, ∀ i ∈ s, Integrable (fun ω => Real.exp (lam * X i ω)) μ)
    (hmgf : ∀ lam > 0, ∀ i ∈ s, (∫ ω, Real.exp (lam * X i ω) ∂μ) ≤
      Real.exp (lam * m + lam ^ 2 * L ^ 2 / 2)) :
    (∫ ω, supMeanFiniteMaximum s hs X ω ∂μ) ≤ m + L * Real.sqrt (2 * Real.log s.card) := by
  have hn : (1 : ℝ) < s.card := by exact_mod_cast (by omega : 1 < s.card)
  have hlog : 0 < Real.log s.card := Real.log_pos hn
  let a := Real.sqrt (2 * Real.log s.card)
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos (by norm_num) hlog)
  have hasq : a ^ 2 = 2 * Real.log s.card := Real.sq_sqrt (by positivity)
  have hl : 0 < a / L := div_pos ha hL
  have hb := supMean_finite_max_bound μ s hs X hXm hX (a / L)
    ((a / L) * m + (a / L) ^ 2 * L ^ 2 / 2) hl (hE _ hl) (hmgf _ hl)
  have he : (Real.log s.card + ((a / L) * m + (a / L) ^ 2 * L ^ 2 / 2)) / (a / L) =
      m + L * a := by
    apply (div_eq_iff (ne_of_gt hl)).mpr
    field_simp [hL.ne']
    nlinarith only [congrArg (fun z : ℝ => z * L) hasq]
  exact hb.trans_eq he

end ASDExplicitGamma.Gaussian
