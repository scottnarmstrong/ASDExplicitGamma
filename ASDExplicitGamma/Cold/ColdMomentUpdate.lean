module

public import ASDExplicitGamma.Cold.ColdCenteredAverage

/-! # The source same-law moment-cap update from actual nonnegative child traces -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- A finite ordinary average preserves an L20 cap without centering. -/
theorem cold_trace_average_lpNorm_le {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ} {M : ℝ}
    (hX : ∀ i, MemLp (X i) 20 ℙ) (hcap : ∀ i, lpNorm (X i) 20 ℙ ≤ M) :
    lpNorm (fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)) 20 ℙ ≤ M := by
  classical
  rw [lpNorm_fun_div_natCast Fintype.card_ne_zero]
  have h := (lpNorm_sum_le (s := Finset.univ) (fun i _ => hX i) (by norm_num : (1:ℝ≥0∞) ≤ 20)).trans
    (Finset.sum_le_sum (fun i _ => hcap i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have he : (fun ω => ∑ i, X i ω) = ∑ i, X i := by funext ω; simp only [Finset.sum_apply]
  rw [he]
  apply (div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  simpa only [mul_comm] using h

/-- The same-law moment update uses only actual child traces, ordinary mean caps and
pathwise subadditivity. The centered decay has exactly the source constant `2*sqrt(19)`. -/
theorem cold_moment_update {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] (color : ι → Fin 4)
    {X : ι → Ω → ℝ} {T : Ω → ℝ} {M D : ℝ}
    (hX : ∀ i, MemLp (X i) 20 ℙ) (hn : ∀ i, ∀ᵐ ω ∂ℙ, 0 ≤ X i ω)
    (hi : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => X i.val) ℙ)
    (hM : 0 ≤ M) (hcap : ∀ i, lpNorm (X i) 20 ℙ ≤ M)
    (hmean : (∑ i, ∫ ω, X i ω ∂ℙ)/(Fintype.card ι:ℝ) ≤ D)
    (hT : ∀ᵐ ω ∂ℙ, 0 ≤ T ω)
    (hsub : ∀ᵐ ω ∂ℙ, T ω ≤ (∑ i, X i ω)/(Fintype.card ι:ℝ)) :
    lpNorm T 20 ℙ ≤ min M (D+min M (2*Real.sqrt 19/Real.sqrt (Fintype.card ι:ℝ)*M)) := by
  classical
  let A := fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)
  let μ := (∑ i, ∫ ω, X i ω ∂ℙ)/(Fintype.card ι:ℝ)
  have hA : MemLp A 20 ℙ := by
    have h := (memLp_finsetSum Finset.univ (fun i _ => hX i)).const_mul ((Fintype.card ι:ℝ)⁻¹)
    simpa only [A,div_eq_mul_inv,mul_comm] using h
  have havg := cold_trace_average_lpNorm_le hX hcap
  have hbase : lpNorm T 20 ℙ ≤ M := (cold_nonnegative_trace_lpNorm_le hA hT hsub).trans havg
  have hD : 0 ≤ D := by
    have hnμ : 0 ≤ μ := div_nonneg (Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (hn i))) (by positivity)
    exact hnμ.trans hmean
  have hdecay := cold_trace_average_fluctuation color hX hn hi hM hcap
  have hTi : lpNorm T 20 ℙ ≤ lpNorm A 20 ℙ := cold_nonnegative_trace_lpNorm_le hA hT hsub
  have hcenter : MemLp (fun ω => A ω-μ) 20 ℙ := hA.sub (memLp_const _)
  have htri := lpNorm_add_le hcenter (g := fun _ => μ) (by norm_num : (1:ℝ≥0∞) ≤ 20)
  have heq : (fun ω => A ω-μ)+(fun _ => μ) = A := by funext ω; simp only [Pi.add_apply,sub_add_cancel]
  rw [heq,lpNorm_const' (by norm_num : (20:ℝ≥0∞) ≠ 0) (by norm_num : (20:ℝ≥0∞) ≠ ⊤)] at htri
  have hnμ : 0 ≤ μ := div_nonneg (Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae (hn i))) (by positivity)
  simp only [Real.norm_eq_abs,abs_of_nonneg hnμ,probReal_univ,Real.one_rpow,mul_one] at htri
  have hdec : lpNorm T 20 ℙ ≤ D+2*Real.sqrt 19/Real.sqrt (Fintype.card ι:ℝ)*M := by
    change lpNorm (fun ω => A ω-μ) 20 ℙ ≤ _ at hdecay
    linarith only [hTi,htri,hdecay,hmean]
  apply le_min hbase
  rw [add_min]
  exact le_min (hbase.trans (le_add_of_nonneg_left hD)) hdec

end ASDExplicitGamma.Cold
