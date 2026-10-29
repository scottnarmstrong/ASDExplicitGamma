module

public import ASDExplicitGamma.Inverse.WeightedLocalizationBernstein

/-! The exact planar partial-block Bernstein terms of QSEP (6). -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Exact QSEP (6) reduction: the true layer volume v stays in the variance
term, while the source maximum partial-block weight is 9*a. -/
theorem localization_partial_block_Lp {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [DecidableEq κ] (mu : Measure Ω) [IsProbabilityMeasure mu]
    (X : ι → Ω → ℝ) (c : ι → κ)
    (hind : ∀ j : κ, iIndepFun (fun i : {i // c i = j} => X i.1) mu)
    (hm : ∀ i, Measurable (X i)) (m : ℕ) (N a v M2m p : ℝ)
    (hN : 0 ≤ N) (ha : 0 ≤ a) (_hv : 0 ≤ v) (hM2m : 0 ≤ M2m) (hp : 2 ≤ p)
    (hcolors : (Fintype.card κ : ℝ) ≤ (7 * N) ^ 2)
    (hX : ∀ i, ∀ᵐ ω ∂mu, 0 ≤ X i ω ∧ X i ω ≤ (4 * N) ^ m)
    (hX2 : ∀ i, moment (X i) 2 mu ≤ M2m)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwmax : ∀ i, w i ≤ 9 * a)
    (hwv : (∑ i, w i) = v) :
    eLpNorm (fun ω => ∑ i, w i * (X i ω - ∫ η, X i η ∂mu)) (ENNReal.ofReal p) mu ≤
      ENNReal.ofReal (4 * Real.sqrt (p * 21 ^ 2 * M2m * N ^ 2 * a * v) +
        4 * p * 21 ^ 2 * 4 ^ m * N ^ (m + 2) * a) := by
  have hh := localization_weighted_Bernstein mu X c hind hm ((4 * N) ^ m) M2m (9 * a) p
    (by positivity) hM2m (by positivity) hp hX hX2 w hw hwmax
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hsq : (∑ i, (w i) ^ 2) ≤ 9 * a * v := by
    simpa only [hwv] using localization_weight_square_sum Finset.univ w (9 * a)
      (fun i _ => hw i) (fun i _ => hwmax i)
  have hprod := mul_le_mul hcolors hsq (Finset.sum_nonneg (fun i _ => sq_nonneg (w i)))
    (by positivity : 0 ≤ (7 * N) ^ 2)
  have hvar : p * (Fintype.card κ : ℝ) * M2m * (∑ i, (w i) ^ 2) ≤
      p * 21 ^ 2 * M2m * N ^ 2 * a * v := by
    calc
      _ = (p * M2m) * ((Fintype.card κ : ℝ) * ∑ i, (w i) ^ 2) := by ring
      _ ≤ (p * M2m) * ((7 * N) ^ 2 * (9 * a * v)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by ring
  have hlin := mul_le_mul_of_nonneg_left hcolors
    (show 0 ≤ 4 * p * ((4 * N) ^ m) * (9 * a) by positivity)
  have hlineq : (4 * p * ((4 * N) ^ m) * (9 * a)) * (7 * N) ^ 2 =
      4 * p * 21 ^ 2 * 4 ^ m * N ^ (m + 2) * a := by
    rw [mul_pow, pow_add N m 2]
    ring
  have hroot := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvar) (by norm_num : (0 : ℝ) ≤ 4)
  rw [hlineq] at hlin
  nlinarith only [hroot, hlin]

end ASDExplicitGamma.Inverse
