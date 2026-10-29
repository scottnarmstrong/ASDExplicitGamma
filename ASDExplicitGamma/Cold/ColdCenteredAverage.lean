module

public import ASDExplicitGamma.Cold.FourColorTwenty
public import ASDExplicitGamma.Cold.LpMonotonicity

/-! # Sharp centered averages of the source nonnegative traces -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The source cell average and its centering commute exactly with the finite mean. -/
theorem cold_average_center_identity {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (μ : ι → ℝ) (ω : Ω) :
    (∑ i, X i ω)/(Fintype.card ι:ℝ)-(∑ i, μ i)/(Fintype.card ι:ℝ) =
      (∑ i, (X i ω-μ i))/(Fintype.card ι:ℝ) := by
  rw [Finset.sum_sub_distrib,sub_div]

/-- Nonnegative actual traces retain the exact constant one in each centered input,
then the four-colour estimate supplies the sharp depth decay. -/
theorem cold_trace_average_fluctuation {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] (color : ι → Fin 4)
    {X : ι → Ω → ℝ} {M : ℝ} (hX : ∀ i, MemLp (X i) 20 ℙ)
    (hn : ∀ i, ∀ᵐ ω ∂ℙ, 0 ≤ X i ω)
    (hi : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => X i.val) ℙ)
    (hM : 0 ≤ M) (hcap : ∀ i, lpNorm (X i) 20 ℙ ≤ M) :
    lpNorm (fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)-
      (∑ i, ∫ a, X i a ∂ℙ)/(Fintype.card ι:ℝ)) 20 ℙ ≤
      2*Real.sqrt 19/Real.sqrt (Fintype.card ι:ℝ)*M := by
  classical
  let Y := fun i ω => X i ω-∫ a, X i a ∂ℙ
  have hY (i : ι) : MemLp (Y i) 20 ℙ := (hX i).sub (memLp_const _)
  have hYi (c : Fin 4) : ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => Y i.val) ℙ := by
    exact (hi c).comp (fun i => fun x : ℝ => x-∫ a, X i.val a ∂ℙ)
      (fun _ => measurable_id.sub measurable_const)
  have hY0 (i : ι) : (∫ ω, Y i ω ∂ℙ) = 0 := by
    have hXi := (hX i).integrable (by norm_num : (1:ℝ≥0∞) ≤ 20)
    dsimp only [Y]
    rw [integral_sub hXi (integrable_const _),integral_const,probReal_univ,one_smul,sub_self]
  have hYcap (i : ι) : lpNorm (Y i) 20 ℙ ≤ M := by
    have hc := lpNorm_sub_mean_le ℙ (p := (20:ℝ)) (by norm_num)
      (by simpa only [ENNReal.ofReal_ofNat] using hX i) (hn i)
    norm_num only [ENNReal.ofReal_ofNat] at hc
    exact hc.trans (hcap i)
  have h := four_color_twenty_centered_average color hY hYi hY0 hM hYcap
  simpa only [cold_average_center_identity,Y] using h

end ASDExplicitGamma.Cold
