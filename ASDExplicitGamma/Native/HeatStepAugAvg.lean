module

public import ASDExplicitGamma.Native.HeatRemainderControlAugmentNorm

/-! Abstract heat-augmented average envelope: a weighted average of nonnegative traces
`T_i(ω,ξ) ≤ (√f_i(ω) + |G_i(ξ)| √(2(b + R_i(ω))))²` on a product probability space has
`‖Σ w_i T_i‖₂₀ ≤ (√y + √(2 b q + 2 ε c))²`, with `y`, `q`, `ε`, `c` the `L^20` caps of the
average `Σ w_i f_i`, of the auxiliary quadratic `Σ w_i G_i²`, of the rare weights `R_i` and of the
squares `G_i²`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory
open scoped ENNReal BigOperators

/-- Weighted Minkowski for a sum of squares. -/
theorem nativeHeatStep_weighted_sq_add_le {ι : Type*} (s : Finset ι) (w a c : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ha : ∀ i ∈ s, 0 ≤ a i) (hc : ∀ i ∈ s, 0 ≤ c i) :
    ∑ i ∈ s, w i * (a i + c i) ^ 2 ≤
      (Real.sqrt (∑ i ∈ s, w i * a i ^ 2) + Real.sqrt (∑ i ∈ s, w i * c i ^ 2)) ^ 2 := by
  have hS1 : 0 ≤ ∑ i ∈ s, w i * a i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hS2 : 0 ≤ ∑ i ∈ s, w i * c i ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have hX0 : 0 ≤ ∑ i ∈ s, w i * (a i * c i) :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (mul_nonneg (ha i hi) (hc i hi))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i) * a i)
    (fun i => Real.sqrt (w i) * c i)
  have e1 : ∑ i ∈ s, (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * c i) =
      ∑ i ∈ s, w i * (a i * c i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have := Real.mul_self_sqrt (hw i hi)
    calc (Real.sqrt (w i) * a i) * (Real.sqrt (w i) * c i)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * (a i * c i) := by ring
      _ = _ := by rw [this]
  have e2 : ∑ i ∈ s, (Real.sqrt (w i) * a i) ^ 2 = ∑ i ∈ s, w i * a i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have e3 : ∑ i ∈ s, (Real.sqrt (w i) * c i) ^ 2 = ∑ i ∈ s, w i * c i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [e1, e2, e3] at hcs
  have hX : ∑ i ∈ s, w i * (a i * c i) ≤
      Real.sqrt (∑ i ∈ s, w i * a i ^ 2) * Real.sqrt (∑ i ∈ s, w i * c i ^ 2) := by
    rw [← Real.sqrt_mul hS1]
    exact Real.le_sqrt_of_sq_le hcs
  have hexp : ∑ i ∈ s, w i * (a i + c i) ^ 2 =
      ∑ i ∈ s, w i * a i ^ 2 + 2 * ∑ i ∈ s, w i * (a i * c i) + ∑ i ∈ s, w i * c i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hexp, add_sq, Real.sq_sqrt hS1, Real.sq_sqrt hS2]
  nlinarith [hX]

/-- The abstract heat-augmented average envelope. -/
theorem nativeHeatStep_avgAug_L20 {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Fintype ι] (μ : Measure Ω) (η : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (w : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (T : ι → Ω × Ξ → ℝ) (f R : ι → Ω → ℝ) (G : ι → Ξ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hTm : ∀ i, AEStronglyMeasurable (T i) (μ.prod η)) (hT0 : ∀ i z, 0 ≤ T i z)
    (hfm : ∀ i, AEStronglyMeasurable (f i) μ) (hf0 : ∀ i ω, 0 ≤ f i ω)
    (hRm : ∀ i, AEStronglyMeasurable (R i) μ) (hR0 : ∀ i ω, 0 ≤ R i ω)
    (hGm : ∀ i, AEStronglyMeasurable (G i) η)
    (hpoint : ∀ᵐ z ∂μ.prod η, ∀ i, T i z ≤
      (Real.sqrt (f i z.1) + |G i z.2| * Real.sqrt (2 * (b + R i z.1))) ^ 2)
    (y q ε c : ℝ) (hy : 0 ≤ y) (hq : 0 ≤ q) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hA0 : eLpNorm (fun ω => ∑ i, w i * f i ω) 20 μ ≤ ENNReal.ofReal y)
    (hQ : eLpNorm (fun ξ => ∑ i, w i * (G i ξ) ^ 2) 20 η ≤ ENNReal.ofReal q)
    (hRn : ∀ i, eLpNorm (R i) 20 μ ≤ ENNReal.ofReal ε)
    (hGn : ∀ i, eLpNorm (fun ξ => (G i ξ) ^ 2) 20 η ≤ ENNReal.ofReal c) :
    eLpNorm (fun z => ∑ i, w i * T i z) 20 (μ.prod η) ≤
      ENNReal.ofReal ((Real.sqrt y + Real.sqrt (2 * b * q + 2 * ε * c)) ^ 2) := by
  classical
  have e20 : (20 : ℝ≥0∞) = ENNReal.ofReal 20 := by simp
  have e40 : (ENNReal.ofReal (2 * 20)) = 40 := by
    rw [show (2 * 20 : ℝ) = 40 by norm_num]; simp
  have hA0' : eLpNorm (fun ω => ∑ i, w i * f i ω) (ENNReal.ofReal 20) μ ≤ ENNReal.ofReal y := by
    rw [← e20]; exact hA0
  have hQ' : eLpNorm (fun ξ => ∑ i, w i * (G i ξ) ^ 2) (ENNReal.ofReal 20) η ≤ ENNReal.ofReal q := by
    rw [← e20]; exact hQ
  have hRn' : ∀ i, eLpNorm (R i) (ENNReal.ofReal 20) μ ≤ ENNReal.ofReal ε := by
    intro i; rw [← e20]; exact hRn i
  have hGn' : ∀ i, eLpNorm (fun ξ => (G i ξ) ^ 2) (ENNReal.ofReal 20) η ≤ ENNReal.ofReal c := by
    intro i; rw [← e20]; exact hGn i
  let A0 : Ω → ℝ := fun ω => ∑ i, w i * f i ω
  let Qf : Ξ → ℝ := fun ξ => ∑ i, w i * (G i ξ) ^ 2
  let W : Ω × Ξ → ℝ := fun z =>
    2 * b * Qf z.2 + 2 * ∑ i, w i * (R i z.1 * (G i z.2) ^ 2)
  have hA0m : AEStronglyMeasurable A0 μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hfm i).const_mul _
  have hA0nn : ∀ ω, 0 ≤ A0 ω := fun ω =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hf0 i ω)
  have hQm : AEStronglyMeasurable Qf η :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => ((hGm i).pow 2).const_mul _
  have hQnn : ∀ ξ, 0 ≤ Qf ξ := fun ξ =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)
  have hRG : ∀ i, AEStronglyMeasurable (fun z : Ω × Ξ => R i z.1 * (G i z.2) ^ 2) (μ.prod η) :=
    fun i => ((hRm i).comp_measurePreserving measurePreserving_fst).mul
      (((hGm i).pow 2).comp_measurePreserving measurePreserving_snd)
  have hWm : AEStronglyMeasurable W (μ.prod η) := by
    refine AEStronglyMeasurable.add ?_ ?_
    · exact (((hQm.comp_measurePreserving measurePreserving_snd)).const_mul _)
    · exact (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hRG i).const_mul _).const_mul _
  have hWnn : ∀ z, 0 ≤ W z := fun z => by
    refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb) (hQnn _)) ?_
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw0 i) (mul_nonneg (hR0 i _) (sq_nonneg _)))
  let F : Ω × Ξ → ℝ := fun z => Real.sqrt (A0 z.1)
  let D : Ω × Ξ → ℝ := fun z => Real.sqrt (W z)
  have hFm : AEStronglyMeasurable F (μ.prod η) :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hA0m).comp_measurePreserving
      measurePreserving_fst
  have hDm : AEStronglyMeasurable D (μ.prod η) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hWm
  have hFD0 : ∀ z, 0 ≤ (F + D) z := fun z =>
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- pathwise envelope
  have hpath : ∀ᵐ z ∂μ.prod η, (∑ i, w i * T i z) ≤ ((F + D) z) ^ 2 := by
    filter_upwards [hpoint] with z hz
    have h1 : ∑ i, w i * T i z ≤
        ∑ i, w i * (Real.sqrt (f i z.1) + |G i z.2| * Real.sqrt (2 * (b + R i z.1))) ^ 2 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz i) (hw0 i)
    refine h1.trans ?_
    have hcs := nativeHeatStep_weighted_sq_add_le Finset.univ w (fun i => Real.sqrt (f i z.1))
      (fun i => |G i z.2| * Real.sqrt (2 * (b + R i z.1))) (fun i _ => hw0 i)
      (fun i _ => Real.sqrt_nonneg _) (fun i _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    refine hcs.trans (le_of_eq ?_)
    have ha : ∑ i, w i * Real.sqrt (f i z.1) ^ 2 = A0 z.1 := by
      apply Finset.sum_congr rfl; intro i _; rw [Real.sq_sqrt (hf0 i _)]
    have hcW : ∑ i, w i * (|G i z.2| * Real.sqrt (2 * (b + R i z.1))) ^ 2 = W z := by
      have hterm : ∀ i, w i * (|G i z.2| * Real.sqrt (2 * (b + R i z.1))) ^ 2 =
          2 * b * (w i * (G i z.2) ^ 2) + 2 * (w i * (R i z.1 * (G i z.2) ^ 2)) := by
        intro i
        have hd : 0 ≤ 2 * (b + R i z.1) := by have := hR0 i z.1; linarith
        rw [mul_pow, sq_abs, Real.sq_sqrt hd]; ring
      simp only [W, Qf]
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [ha, hcW]
    simp only [F, D, Pi.add_apply]
  -- norm of W
  have hWbound : eLpNorm W (ENNReal.ofReal 20) (μ.prod η) ≤
      ENNReal.ofReal (2 * b * q + 2 * ε * c) := by
    let P1 : Ω × Ξ → ℝ := fun z => Qf z.2
    let P2 : Ω × Ξ → ℝ := fun z => ∑ i, w i * (R i z.1 * (G i z.2) ^ 2)
    have hP1 : AEStronglyMeasurable P1 (μ.prod η) := hQm.comp_measurePreserving measurePreserving_snd
    have hP2 : AEStronglyMeasurable P2 (μ.prod η) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hRG i).const_mul _
    have hWeq : W = fun z => (2 * b) • P1 z + (2 : ℝ) • P2 z := by
      funext z; simp [W, P1, P2, smul_eq_mul]
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 20 := by simp
    have hsum := eLpNorm_add_le (f := fun z => (2 * b) • P1 z) (g := fun z => (2 : ℝ) • P2 z)
      (μ := μ.prod η) hp1
    rw [hWeq]
    have hsum' : eLpNorm (fun z => (2 * b) • P1 z + (2 : ℝ) • P2 z) (ENNReal.ofReal 20) (μ.prod η) ≤ _ := hsum
    refine hsum'.trans ?_
    have n1 : eLpNorm (fun z => (2 * b) • P1 z) (ENNReal.ofReal 20) (μ.prod η) ≤
        ENNReal.ofReal (2 * b * q) := by
      change eLpNorm ((2 * b) • P1) _ _ ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by positivity)]
      have : eLpNorm P1 (ENNReal.ofReal 20) (μ.prod η) = eLpNorm Qf (ENNReal.ofReal 20) η :=
        eLpNorm_comp_measurePreserving (p := ENNReal.ofReal 20) hQm measurePreserving_snd
      rw [this]
      calc ENNReal.ofReal (2 * b) * eLpNorm Qf (ENNReal.ofReal 20) η
          ≤ ENNReal.ofReal (2 * b) * ENNReal.ofReal q := mul_le_mul' le_rfl hQ'
        _ = ENNReal.ofReal (2 * b * q) := (ENNReal.ofReal_mul (by positivity)).symm
    have hs2 : eLpNorm P2 (ENNReal.ofReal 20) (μ.prod η) ≤ ENNReal.ofReal (ε * c) := by
      have h1 := eLpNorm_sum_le (μ := μ.prod η) (s := Finset.univ)
        (f := fun i z => w i * (R i z.1 * (G i z.2) ^ 2)) hp1
      have hP2eq : P2 = ∑ i : ι, (fun z : Ω × Ξ => w i * (R i z.1 * (G i z.2) ^ 2)) := by
        funext z; simp [P2, Finset.sum_apply]
      rw [hP2eq]
      refine h1.trans ?_
      have h2 : ∀ i, eLpNorm (fun z : Ω × Ξ => w i * (R i z.1 * (G i z.2) ^ 2))
          (ENNReal.ofReal 20) (μ.prod η) ≤ ENNReal.ofReal (w i) * ENNReal.ofReal (ε * c) := by
        intro i
        have : (fun z : Ω × Ξ => w i * (R i z.1 * (G i z.2) ^ 2)) =
            (w i) • (fun z : Ω × Ξ => R i z.1 * (G i z.2) ^ 2) := by
          funext z; simp [smul_eq_mul]
        rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw0 i),
          nativeHeat_independent_product_Lp μ η (R i) (fun ξ => (G i ξ) ^ 2) (hRm i)
            ((hGm i).pow 2) 20 (by norm_num), ENNReal.ofReal_mul hε]
        exact mul_le_mul' le_rfl (mul_le_mul' (hRn' i) (hGn' i))
      refine (Finset.sum_le_sum fun i _ => h2 i).trans ?_
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i), hw1]
      simp
    have n2 : eLpNorm (fun z => (2 : ℝ) • P2 z) (ENNReal.ofReal 20) (μ.prod η) ≤
        ENNReal.ofReal (2 * ε * c) := by
      change eLpNorm ((2 : ℝ) • P2) _ _ ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num)]
      calc ENNReal.ofReal 2 * eLpNorm P2 (ENNReal.ofReal 20) (μ.prod η)
          ≤ ENNReal.ofReal 2 * ENNReal.ofReal (ε * c) := mul_le_mul' le_rfl hs2
        _ = ENNReal.ofReal (2 * ε * c) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf
    calc _ ≤ ENNReal.ofReal (2 * b * q) + ENNReal.ofReal (2 * ε * c) := add_le_add n1 n2
      _ = ENNReal.ofReal (2 * b * q + 2 * ε * c) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  -- assemble
  have hAvgm : AEStronglyMeasurable (fun z => ∑ i, w i * T i z) (μ.prod η) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hTm i).const_mul _
  have hmono : eLpNorm (fun z => ∑ i, w i * T i z) (ENNReal.ofReal 20) (μ.prod η) ≤
      eLpNorm (fun z => ((F + D) z) ^ 2) (ENNReal.ofReal 20) (μ.prod η) := by
    refine eLpNorm_mono_ae hAvgm ?_
    filter_upwards [hpath] with z hz
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hT0 i z)),
      Real.norm_of_nonneg (sq_nonneg _)]
    exact hz
  rw [nativeHeat_square_Lp (μ.prod η) (F + D) (hFm.add hDm) hFD0 20 (by norm_num)] at hmono
  have hp40 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * 20) := by
    rw [e40]; norm_num
  have hadd := eLpNorm_add_le (f := F) (g := D) (μ := μ.prod η) hp40
  have hFn : eLpNorm F (ENNReal.ofReal (2 * 20)) (μ.prod η) ≤ ENNReal.ofReal (Real.sqrt y) := by
    have hrt : AEStronglyMeasurable (fun ω => Real.sqrt (A0 ω)) μ :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hA0m
    rw [show F = (fun ω => Real.sqrt (A0 ω)) ∘ Prod.fst from rfl,
      eLpNorm_comp_measurePreserving hrt measurePreserving_fst,
      nativeHeat_sqrt_Lp μ A0 hA0m hA0nn 20 (by norm_num)]
    have hh : ENNReal.ofReal (Real.sqrt y) = ENNReal.ofReal y ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), Real.sqrt_eq_rpow]
    rw [hh]
    exact ENNReal.rpow_le_rpow hA0' (by norm_num)
  have hDn : eLpNorm D (ENNReal.ofReal (2 * 20)) (μ.prod η) ≤
      ENNReal.ofReal (Real.sqrt (2 * b * q + 2 * ε * c)) := by
    show eLpNorm (fun z => Real.sqrt (W z)) _ _ ≤ _
    have hpos : 0 ≤ 2 * b * q + 2 * ε * c := by positivity
    have hh : ENNReal.ofReal (Real.sqrt (2 * b * q + 2 * ε * c)) =
        ENNReal.ofReal (2 * b * q + 2 * ε * c) ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hpos (by norm_num), Real.sqrt_eq_rpow]
    rw [nativeHeat_sqrt_Lp (μ.prod η) W hWm hWnn 20 (by norm_num), hh]
    exact ENNReal.rpow_le_rpow hWbound (by norm_num)
  have hfin := hmono.trans (pow_le_pow_left' (hadd.trans (add_le_add hFn hDn)) 2)
  rw [e20]
  refine hfin.trans_eq ?_
  rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]

end ASDExplicitGamma.Native

end
