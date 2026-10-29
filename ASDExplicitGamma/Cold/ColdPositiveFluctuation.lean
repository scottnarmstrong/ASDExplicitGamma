module

public import ASDExplicitGamma.Cold.ColdMomentCaps

/-! # Positive fluctuations around a deterministic ordinary-mean cap -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- A finite actual nonnegative trace average has the source positive-fluctuation cap.
The deterministic mean cap remains outside every later spatial maximum. -/
theorem cold_positive_fluctuation_cap {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] (color : ι → Fin 4)
    {X : ι → Ω → ℝ} {M D : ℝ} (hX : ∀ i, MemLp (X i) 20 ℙ)
    (hn : ∀ i, ∀ᵐ ω ∂ℙ, 0 ≤ X i ω)
    (hi : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => X i.val) ℙ)
    (hM : 0 ≤ M) (hcap : ∀ i, lpNorm (X i) 20 ℙ ≤ M)
    (hmean : (∑ i, ∫ ω, X i ω ∂ℙ)/(Fintype.card ι:ℝ) ≤ D) :
    lpNorm (fun ω => max ((∑ i, X i ω)/(Fintype.card ι:ℝ)-D) 0) 20 ℙ ≤
      min M (2*Real.sqrt 19/Real.sqrt (Fintype.card ι:ℝ)*M) := by
  classical
  let A := fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)
  let μ := (∑ i, ∫ ω, X i ω ∂ℙ)/(Fintype.card ι:ℝ)
  have hA : MemLp A 20 ℙ := by
    have h := (memLp_finsetSum Finset.univ (fun i _ => hX i)).const_mul ((Fintype.card ι:ℝ)⁻¹)
    simpa only [A,div_eq_mul_inv,mul_comm] using h
  have hnμ : 0 ≤ μ := div_nonneg (Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (hn i))) (by positivity)
  have hD : 0 ≤ D := hnμ.trans hmean
  have hAn : ∀ᵐ ω ∂ℙ, 0 ≤ A ω := by
    filter_upwards [ae_all_iff.mpr hn] with ω hω
    exact div_nonneg (Finset.sum_nonneg (fun i _ => hω i)) (by positivity)
  apply le_min
  · refine (cold_lpNorm_mono_ae hA ?_).trans (cold_trace_average_lpNorm_le hX hcap)
    filter_upwards [hAn] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs,abs_of_nonneg hω]
    exact max_le (sub_le_self _ hD) hω
  · have hm : MemLp (fun ω => A ω-μ) 20 ℙ := hA.sub (memLp_const _)
    refine (cold_lpNorm_mono_ae hm ?_).trans (cold_trace_average_fluctuation color hX hn hi hM hcap)
    filter_upwards with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),Real.norm_eq_abs]
    exact max_le ((sub_le_sub_left hmean _).trans (le_abs_self _)) (abs_nonneg _)

end ASDExplicitGamma.Cold
