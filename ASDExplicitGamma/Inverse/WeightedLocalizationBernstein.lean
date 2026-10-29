module

public import ASDExplicitGamma.Inverse.WeightedLocalizationCentering

/-! The source weighted colored Bernstein envelope at every real order p>=2. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The Bernstein bound, retaining the exact squared-weight sum. Independence is required
only within deterministic color classes. -/
theorem localization_weighted_Bernstein {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : ι → Ω → ℝ) (c : ι → κ)
    (hind : ∀ j : κ, iIndepFun (fun i : {i // c i = j} => X i.1) mu)
    (hm : ∀ i, Measurable (X i)) (M v0 W p : ℝ)
    (hM : 0 ≤ M) (hv0 : 0 ≤ v0) (hW : 0 ≤ W) (hp : 2 ≤ p)
    (hX : ∀ i, ∀ᵐ ω ∂mu, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hX2 : ∀ i, moment (X i) 2 mu ≤ v0)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) :
    eLpNorm (fun ω => ∑ i, w i * (X i ω - ∫ η, X i η ∂mu)) (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (4 * Real.sqrt (p * (Fintype.card κ : ℝ) * v0 * ∑ i, (w i) ^ 2) +
        4 * p * (Fintype.card κ : ℝ) * M * W) := by
  let Y : ι → Ω → ℝ := fun i ω => w i * (X i ω - ∫ η, X i η ∂mu)
  let V : κ → ℝ := fun j => v0 * ∑ i : {i // c i = j}, (w i.1) ^ 2
  have hi (i : ι) := (localization_bounded_mean mu (X i) (hm i) M hM (hX i)).1
  have hYm (i : ι) : Measurable (Y i) := ((hm i).sub_const _).const_mul _
  have hYi (j : κ) : iIndepFun (fun i : {i // c i = j} => Y i.1) mu :=
    (hind j).comp (fun i x => w i.1 * (x - ∫ η, X i.1 η ∂mu))
      (fun i => measurable_const.mul (measurable_id.sub_const _))
  have hYb (i : ι) : ∀ᵐ ω ∂mu, |Y i ω| ≤ M * W := by
    filter_upwards [localization_centered_abs_bound mu (X i) (hm i) M hM (hX i)] with ω hω
    change |w i * (X i ω - ∫ η, X i η ∂mu)| ≤ M * W
    rw [abs_mul, abs_of_nonneg (hw i)]
    exact (mul_le_mul_of_nonneg_left hω (hw i)).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hwW i) hM)
  have hYmean (i : ι) : (∫ ω, Y i ω ∂mu) = 0 :=
    localization_weighted_centered_mean mu (X i) (hi i) (w i)
  have hVm (j : κ) : (∑ i : {i // c i = j}, moment (Y i.1) 2 mu) ≤ V j := by
    dsimp only [V]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => by
      simpa only [mul_comm] using localization_weighted_centered_moment mu (X i.1) (hm i.1)
        (w i.1) v0 (hX2 i.1))
  have hV0 (j : κ) : 0 ≤ V j := by dsimp only [V]; positivity
  have hh := localization_colored_Lp mu Y c hYi hYm (M * W) p (mul_nonneg hM hW)
    (by linarith) hYb hYmean V hV0 hVm
  have hVs : (∑ j, V j) = v0 * ∑ i, (w i) ^ 2 := by
    dsimp only [V]
    rw [← Finset.mul_sum, Fintype.sum_fiberwise c (fun i => (w i) ^ 2)]
  rw [hVs] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hroot : Real.sqrt p * Real.sqrt (v0 * ∑ i, (w i) ^ 2) * Real.sqrt (Fintype.card κ : ℝ) =
      Real.sqrt (p * (Fintype.card κ : ℝ) * v0 * ∑ i, (w i) ^ 2) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ p), ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  have hroot0 := Real.sqrt_nonneg (p * (Fintype.card κ : ℝ) * v0 * ∑ i, (w i) ^ 2)
  have hlinear : 0 ≤ (M * W) * p * (Fintype.card κ : ℝ) := by positivity
  have he : 2 * Real.sqrt p * Real.sqrt (v0 * ∑ i, (w i) ^ 2) * Real.sqrt (Fintype.card κ : ℝ) =
      2 * Real.sqrt (p * (Fintype.card κ : ℝ) * v0 * ∑ i, (w i) ^ 2) := by
    calc
      _ = 2 * (Real.sqrt p * Real.sqrt (v0 * ∑ i, (w i) ^ 2) * Real.sqrt (Fintype.card κ : ℝ)) := by ring
      _ = _ := congrArg (fun x : ℝ => 2 * x) hroot
  rw [he]
  nlinarith only [hroot0, hlinear]

end ASDExplicitGamma.Inverse
