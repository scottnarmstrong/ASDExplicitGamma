module

public import ASDExplicitGamma.Inverse.ClippedMatrixSubGaussian
public import ASDExplicitGamma.Inverse.WeightedLocalizationColors

/-! Hoeffding at every real order for deterministically colored matrix entries. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- Centered independent bounded entries retain the exact squared-weight sum,
with no linear Bernstein remainder. -/
theorem clipped_independent_entry_Lp {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ)
    (hind : iIndepFun X μ) (hm : ∀ i, Measurable (X i)) (G : ℝ) (hG : 0 ≤ G)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ G) (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2*G*Real.sqrt p*Real.sqrt (∑ i, (w i)^2)) := by
  let Y : I → Ω → ℝ := fun i ω => w i*(X i ω-∫ ζ, X i ζ ∂μ)
  let c : I → ℝ≥0 := fun i => ⟨(w i)^2*G^2,by positivity⟩
  have hc (i : I) : HasSubgaussianMGF (Y i) (c i) μ := by
    have h0 := hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable
      ((hb i).mono (fun ω hω => abs_le.mp hω))
    have h1 := h0.const_mul (w i)
    convert h1 using 1
    apply NNReal.eq
    change (w i)^2*G^2 = (w i)^2*(|G- -G|/2)^2
    rw [abs_of_nonneg (by linarith only [hG] : 0 ≤ G- -G)]
    ring
  have hi : iIndepFun Y μ := hind.comp (fun i x => w i*(x-∫ ζ, X i ζ ∂μ))
    (fun _ => measurable_const.mul (measurable_id.sub_const _))
  have hs : HasSubgaussianMGF (fun ω => ∑ i, Y i ω) (∑ i, c i) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hi (fun i _ => hc i)
  have hh := clipped_subGaussian_Lp μ (fun ω => ∑ i, Y i ω) (∑ i, c i) hs p hp
  apply hh.trans_eq
  congr 1
  have he : ((∑ i, c i : ℝ≥0):ℝ) = G^2*∑ i, (w i)^2 := by
    rw [NNReal.coe_sum]
    simp only [c,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (w i)^2*G^2=G^2*(w i)^2
    ring
  rw [he,Real.sqrt_mul (sq_nonneg G),Real.sqrt_sq hG]
  ring

/-- The scalar Hoeffding step, with joint independence only inside each
fixed color. All real p>=1 are covered, and weights stay literal. -/
theorem clipped_colored_entry_Lp {Ω I K : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype K] [DecidableEq K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : I → Ω → ℝ) (color : I → K)
    (hind : ∀ k, iIndepFun (fun i : {i // color i=k} => X i.1) μ)
    (hm : ∀ i, Measurable (X i)) (G : ℝ) (hG : 0 ≤ G)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ G) (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2*G*Real.sqrt p*Real.sqrt (∑ i, (w i)^2)*Real.sqrt (Fintype.card K:ℝ)) := by
  let C : K → Ω → ℝ := fun k ω => ∑ i : {i // color i=k}, w i.1*(X i.1 ω-∫ ζ, X i.1 ζ ∂μ)
  let V : K → ℝ := fun k => ∑ i : {i // color i=k}, (w i.1)^2
  have hc (k : K) := clipped_independent_entry_Lp μ (fun i : {i // color i=k} => X i.1)
    (hind k) (fun i => hm i.1) G hG (fun i => hb i.1) (fun i => w i.1) p hp
  have he : (fun ω => ∑ i, w i*(X i ω-∫ ζ, X i ζ ∂μ)) = ∑ k, C k := by
    funext ω
    simp only [Finset.sum_apply,C]
    exact (Fintype.sum_fiberwise color (fun i => w i*(X i ω-∫ ζ, X i ζ ∂μ))).symm
  rw [he]
  apply (eLpNorm_sum_le (ENNReal.one_le_ofReal.mpr hp)).trans
  calc
    _ ≤ ∑ k, ENNReal.ofReal (2*G*Real.sqrt p*Real.sqrt (V k)) :=
      Finset.sum_le_sum (fun k _ => hc k)
    _ = ENNReal.ofReal (∑ k, 2*G*Real.sqrt p*Real.sqrt (V k)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      have hs := mul_le_mul_of_nonneg_left (localization_color_sqrt_sum V (fun _ => by dsimp [V]; positivity))
        (show 0 ≤ 2*G*Real.sqrt p by positivity)
      have hV : (∑ k, V k) = ∑ i, (w i)^2 := Fintype.sum_fiberwise color (fun i => (w i)^2)
      simpa only [hV,mul_assoc] using hs

end ASDExplicitGamma.Inverse
