/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-! Hölder and Minkowski arithmetic for the one-load consumer of the
smooth-feedback estimate. Everything here is pure analysis on a probability
space; the geometric input enters only through the stated hypotheses. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory
open scoped ENNReal

noncomputable section

section Basic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy--Schwarz for the geometric mean of two integrable nonnegative
measurable functions. -/
theorem integral_sqrt_mul_le [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) :
    ∫ ω, Real.sqrt (X ω * Y ω) ∂μ ≤
      Real.sqrt ((∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)) := by
  have hp : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hsq (Z : Ω → ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω) (hZm : Measurable Z) (hZi : Integrable Z μ) :
      MemLp (fun ω => Real.sqrt (Z ω)) (ENNReal.ofReal 2) μ := by
    have : ENNReal.ofReal 2 = 2 := by norm_num
    rw [this]
    rw [memLp_two_iff_integrable_sq (hZm.sqrt.aestronglyMeasurable)]
    refine hZi.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Real.sq_sqrt (hZ0 ω)]
  have hI := integral_mul_le_Lp_mul_Lq_of_nonneg hp
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (X ω))
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (Y ω))
    (hsq X hX0 hXm hXi) (hsq Y hY0 hYm hYi)
  have h1 : ∫ ω, Real.sqrt (X ω * Y ω) ∂μ =
      ∫ ω, Real.sqrt (X ω) * Real.sqrt (Y ω) ∂μ := by
    congr 1
    funext ω
    exact Real.sqrt_mul (hX0 ω) (Y ω)
  have h2 (Z : Ω → ℝ) (hZ0 : ∀ ω, 0 ≤ Z ω) :
      (∫ ω, Real.sqrt (Z ω) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
        Real.sqrt (∫ ω, Z ω ∂μ) := by
    have : (fun ω => Real.sqrt (Z ω) ^ (2 : ℝ)) = Z := by
      funext ω
      rw [Real.rpow_two, Real.sq_sqrt (hZ0 ω)]
    rw [this, Real.sqrt_eq_rpow]
  rw [h1]
  refine hI.trans ?_
  rw [h2 X hX0, h2 Y hY0, ← Real.sqrt_mul (integral_nonneg hX0)]

theorem rpow_integral_le_of_eLpNorm {f : Ω → ℝ} {p e : ℝ} (hp : 0 < p) (he : 0 ≤ e)
    (hf0 : ∀ ω, 0 ≤ f ω) (hmem : MemLp f (ENNReal.ofReal p) μ)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal e) :
    (∫ ω, f ω ^ p ∂μ) ^ (1 / p) ≤ e := by
  have h0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have h1 := hmem.eLpNorm_eq_integral_rpow_norm h0 ENNReal.ofReal_ne_top
  rw [h1, ENNReal.toReal_ofReal hp.le] at h
  have hnn : 0 ≤ (∫ ω, ‖f ω‖ ^ p ∂μ) ^ p⁻¹ :=
    Real.rpow_nonneg (integral_nonneg fun ω => by positivity) _
  rw [ENNReal.ofReal_le_ofReal_iff he] at h
  have hn : (fun ω => ‖f ω‖ ^ p) = fun ω => f ω ^ p := by
    funext ω; rw [Real.norm_of_nonneg (hf0 ω)]
  rw [hn] at h
  simpa only [one_div] using h

/-- Hölder with the `L^128` / `L^(128/127)` pair used by the OLD bank. -/
theorem integral_mul_le_128 [IsFiniteMeasure μ] {R G : Ω → ℝ} {ε g : ℝ}
    (hRm : Measurable R) (hGm : Measurable G) (hR0 : ∀ ω, 0 ≤ R ω) (hG0 : ∀ ω, 0 ≤ G ω)
    (hε : 0 ≤ ε) (hg : 0 ≤ g)
    (hR : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hG : eLpNorm G (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal g) :
    ∫ ω, R ω * G ω ∂μ ≤ ε * g := by
  have hpq : (128 : ℝ).HolderConjugate (128 / 127) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h128 : ENNReal.ofReal (128 : ℝ) = 128 := by norm_num
  have hRmem : MemLp R (ENNReal.ofReal 128) μ := by
    rw [h128]
    exact memLp_iff.mpr (hR.trans_lt ENNReal.ofReal_lt_top)
  have hGmem : MemLp G (ENNReal.ofReal (128 / 127)) μ :=
    memLp_iff.mpr (hG.trans_lt ENNReal.ofReal_lt_top)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hR0) (Filter.Eventually.of_forall hG0) hRmem hGmem
  have hRn := rpow_integral_le_of_eLpNorm (by norm_num : (0 : ℝ) < 128) hε hR0 hRmem
    (by rw [h128]; exact hR)
  have hGn := rpow_integral_le_of_eLpNorm (by norm_num : (0 : ℝ) < 128 / 127) hg hG0 hGmem hG
  refine hH.trans ?_
  exact mul_le_mul hRn hGn (Real.rpow_nonneg (integral_nonneg fun ω => by
    have := hG0 ω; positivity) _) hε

theorem integrable_mul_128 [IsFiniteMeasure μ] {R G : Ω → ℝ}
    (hRm : Measurable R) (hGm : Measurable G) {ε g : ℝ}
    (hR : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hG : eLpNorm G (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal g) :
    Integrable (fun ω => R ω * G ω) μ := by
  have hpq : (128 : ℝ).HolderConjugate (128 / 127) :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h128 : ENNReal.ofReal (128 : ℝ) = 128 := by norm_num
  have hRmem : MemLp R (ENNReal.ofReal 128) μ := by
    rw [h128]
    exact memLp_iff.mpr (hR.trans_lt ENNReal.ofReal_lt_top)
  have hGmem : MemLp G (ENNReal.ofReal (128 / 127)) μ :=
    memLp_iff.mpr (hG.trans_lt ENNReal.ofReal_lt_top)
  haveI : ENNReal.HolderTriple (ENNReal.ofReal 128) (ENNReal.ofReal (128 / 127)) 1 := by
    simpa using hpq.ennrealOfReal
  exact hRmem.integrable_mul hGmem

/-- Jensen for the square root on a probability space. -/
theorem integral_sqrt_le [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZm : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω) (hZi : Integrable Z μ) :
    ∫ ω, Real.sqrt (Z ω) ∂μ ≤ Real.sqrt (∫ ω, Z ω ∂μ) := by
  have := integral_sqrt_mul_le (μ := μ) hZm measurable_const hZ0 (fun _ => zero_le_one)
    hZi (integrable_const (1 : ℝ))
  simpa using this

/-- Expectation of `(√X+√Y)²`. -/
theorem integral_sqrt_add_sq_le [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) :
    Integrable (fun ω => (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2) μ ∧
    ∫ ω, (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2 ∂μ ≤
      (Real.sqrt (∫ ω, X ω ∂μ) + Real.sqrt (∫ ω, Y ω ∂μ)) ^ 2 := by
  have hexp (ω : Ω) : (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2 =
      X ω + Y ω + 2 * Real.sqrt (X ω * Y ω) := by
    rw [add_sq, Real.sq_sqrt (hX0 ω), Real.sq_sqrt (hY0 ω),
      Real.sqrt_mul (hX0 ω)]
    ring
  have hcross : Integrable (fun ω => Real.sqrt (X ω * Y ω)) μ := by
    refine Integrable.mono' ((hXi.add hYi).div_const 2)
      ((hXm.mul hYm).sqrt.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    show Real.sqrt (X ω * Y ω) ≤ (X ω + Y ω) / 2
    have h0 := hX0 ω
    have h1 := hY0 ω
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg (X ω - Y ω)]⟩
  have hint : Integrable (fun ω => (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2) μ := by
    have := (hXi.add hYi).add (hcross.const_mul 2)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, hexp]
  refine ⟨hint, ?_⟩
  have hI : ∫ ω, (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2 ∂μ =
      ∫ ω, X ω ∂μ + ∫ ω, Y ω ∂μ + 2 * ∫ ω, Real.sqrt (X ω * Y ω) ∂μ := by
    simp_rw [hexp]
    have hXY : Integrable (fun ω => X ω + Y ω) μ := hXi.add hYi
    rw [integral_add hXY (hcross.const_mul 2), integral_add hXi hYi,
      integral_const_mul]
  rw [hI]
  have hcs := integral_sqrt_mul_le hXm hYm hX0 hY0 hXi hYi
  have hxn : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg (fun ω => hX0 ω)
  have hyn : 0 ≤ ∫ ω, Y ω ∂μ := integral_nonneg (fun ω => hY0 ω)
  have h1 := Real.sq_sqrt hxn
  have h2 := Real.sq_sqrt hyn
  have h3 : Real.sqrt ((∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)) =
      Real.sqrt (∫ ω, X ω ∂μ) * Real.sqrt (∫ ω, Y ω ∂μ) := Real.sqrt_mul hxn _
  rw [h3] at hcs
  nlinarith

/-- Optimizing a family of upper bounds `(1+t)a+(1+1/t)c`. -/
theorem inf_bound {r a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → r ≤ (1 + t) * a + (1 + 1 / t) * c) :
    r ≤ (Real.sqrt a + Real.sqrt c) ^ 2 := by
  have hsa := Real.sq_sqrt ha
  have hsc := Real.sq_sqrt hc
  by_cases hA : a = 0
  · subst hA
    simp only [Real.sqrt_zero, zero_add]
    rw [Real.sq_sqrt hc]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hC : c = 0
    · subst hC
      have := h 1 one_pos
      simp at this
      linarith
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hC)
      have := h (c / ε) (div_pos hcpos hε)
      have h1 : (1 + 1 / (c / ε)) * c = c + ε := by field_simp
      linarith
  · have hApos : 0 < a := lt_of_le_of_ne ha (Ne.symm hA)
    by_cases hC : c = 0
    · subst hC
      simp only [Real.sqrt_zero, add_zero]
      rw [Real.sq_sqrt ha]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := h (ε / a) (div_pos hε hApos)
      have h1 : (1 + ε / a) * a = a + ε := by field_simp
      linarith
    · have hCpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hC)
      have hsApos : 0 < Real.sqrt a := Real.sqrt_pos.mpr hApos
      have hsCpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hCpos
      have := h (Real.sqrt c / Real.sqrt a) (div_pos hsCpos hsApos)
      have e1 : (1 + Real.sqrt c / Real.sqrt a) * a + (1 + 1 / (Real.sqrt c / Real.sqrt a)) * c =
          (Real.sqrt a + Real.sqrt c) ^ 2 := by
        field_simp
        nlinarith [hsa, hsc]
      linarith

/-- Linear combinations in `L^q`. -/
theorem eLpNorm_lincomb_le {q : ℝ≥0∞} (hq : 1 ≤ q) {X Y : Ω → ℝ} {α β a c : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha0 : 0 ≤ a) (hc0 : 0 ≤ c)
    (hX : eLpNorm X q μ ≤ ENNReal.ofReal a) (hY : eLpNorm Y q μ ≤ ENNReal.ofReal c) :
    eLpNorm (fun ω => α * X ω + β * Y ω) q μ ≤ ENNReal.ofReal (α * a + β * c) := by
  have h1 : (fun ω => α * X ω + β * Y ω) = α • X + β • Y := by
    funext ω; simp
  rw [h1]
  refine (eLpNorm_add_le hq).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const_smul]
  have ha : ‖α‖ₑ = ENNReal.ofReal α := by
    rw [Real.enorm_eq_ofReal hα]
  have hb : ‖β‖ₑ = ENNReal.ofReal β := by
    rw [Real.enorm_eq_ofReal hβ]
  rw [ha, hb]
  rw [ENNReal.ofReal_add (mul_nonneg hα ha0) (mul_nonneg hβ hc0),
    ENNReal.ofReal_mul hα, ENNReal.ofReal_mul hβ]
  exact add_le_add (mul_le_mul_right hX _) (mul_le_mul_right hY _)

/-- `L^q` bound for `(√X+√Y)²`. -/
theorem eLpNorm_Eb_le {q : ℝ≥0∞} (hq : 1 ≤ q) {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) {a c : ℝ} (ha0 : 0 ≤ a) (hc0 : 0 ≤ c)
    (hX : eLpNorm X q μ ≤ ENNReal.ofReal a) (hY : eLpNorm Y q μ ≤ ENNReal.ofReal c) :
    eLpNorm (fun ω => (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2) q μ ≤
      ENNReal.ofReal ((Real.sqrt a + Real.sqrt c) ^ 2) := by
  have hEm : Measurable (fun ω => (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2) :=
    (hXm.sqrt.add hYm.sqrt).pow_const 2
  have hpt (t : ℝ) (ht : 0 < t) (ω : Ω) :
      (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2 ≤ (1 + t) * X ω + (1 + 1 / t) * Y ω := by
    have h1 := Real.sq_sqrt (hX0 ω)
    have h2 := Real.sq_sqrt (hY0 ω)
    have h3 : 0 ≤ Real.sqrt (X ω) := Real.sqrt_nonneg _
    have h4 : 0 ≤ Real.sqrt (Y ω) := Real.sqrt_nonneg _
    have h5 : 2 * Real.sqrt (X ω) * Real.sqrt (Y ω) ≤
        t * Real.sqrt (X ω) ^ 2 + Real.sqrt (Y ω) ^ 2 / t := by
      rw [← sub_nonneg]
      have : t * Real.sqrt (X ω) ^ 2 + Real.sqrt (Y ω) ^ 2 / t -
          2 * Real.sqrt (X ω) * Real.sqrt (Y ω) =
          (t * Real.sqrt (X ω) - Real.sqrt (Y ω)) ^ 2 / t := by
        field_simp; ring
      rw [this]; positivity
    rw [h1, h2] at h5
    have e1 : (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2 =
        X ω + Y ω + 2 * Real.sqrt (X ω) * Real.sqrt (Y ω) := by
      rw [add_sq, h1, h2]; ring
    have e2 : (1 + 1 / t) * Y ω = Y ω + Y ω / t := by field_simp
    rw [e1, e2]
    nlinarith [h5]
  have hfin : eLpNorm (fun ω => (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2) q μ ≠ ∞ := by
    have := eLpNorm_mono_real (p := q) (μ := μ) hEm.aestronglyMeasurable
      (g := fun ω => (1 + 1) * X ω + (1 + 1 / 1) * Y ω) (fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt 1 one_pos ω)
    have h2 := eLpNorm_lincomb_le (μ := μ) hq (X := X) (Y := Y) (α := 1 + 1)
      (β := 1 + 1 / 1) (by norm_num) (by norm_num) ha0 hc0 hX hY
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (this.trans h2)
  set r := (eLpNorm (fun ω => (Real.sqrt (X ω) + Real.sqrt (Y ω)) ^ 2) q μ).toReal with hr
  have hrle : r ≤ (Real.sqrt a + Real.sqrt c) ^ 2 := by
    apply inf_bound ha0 hc0
    intro t ht
    have h1 := eLpNorm_mono_real (p := q) (μ := μ) hEm.aestronglyMeasurable
      (g := fun ω => (1 + t) * X ω + (1 / 1 + 1 / t) * Y ω) (fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        have := hpt t ht ω
        simpa using this)
    have h2 := eLpNorm_lincomb_le (μ := μ) hq (X := X) (Y := Y) (α := 1 + t)
      (β := 1 / 1 + 1 / t) (by positivity) (by positivity) ha0 hc0 hX hY
    have h3 := h1.trans h2
    have h4 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    rw [ENNReal.toReal_ofReal (by positivity)] at h4
    simpa using h4
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hrle

theorem integral_add6 {f1 f2 f3 f4 f5 f6 : Ω → ℝ}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (h6 : Integrable f6 μ) :
    ∫ x, (f1 x + f2 x + f3 x + f4 x + f5 x + f6 x) ∂μ =
      ∫ x, f1 x ∂μ + ∫ x, f2 x ∂μ + ∫ x, f3 x ∂μ + ∫ x, f4 x ∂μ + ∫ x, f5 x ∂μ +
        ∫ x, f6 x ∂μ := by
  have a12 : Integrable (fun x => f1 x + f2 x) μ := h1.add h2
  have a123 : Integrable (fun x => f1 x + f2 x + f3 x) μ := a12.add h3
  have a1234 : Integrable (fun x => f1 x + f2 x + f3 x + f4 x) μ := a123.add h4
  have a12345 : Integrable (fun x => f1 x + f2 x + f3 x + f4 x + f5 x) μ := a1234.add h5
  rw [integral_add a12345 h6, integral_add a1234 h5, integral_add a123 h4,
    integral_add a12 h3, integral_add h1 h2]

theorem integrable_sqrt_mul [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hXm : Measurable X) (hYm : Measurable Y) (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) :
    Integrable (fun ω => Real.sqrt (X ω * Y ω)) μ := by
  refine Integrable.mono' ((hXi.add hYi).div_const 2)
    ((hXm.mul hYm).sqrt.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  show Real.sqrt (X ω * Y ω) ≤ (X ω + Y ω) / 2
  have h0 := hX0 ω
  have h1 := hY0 ω
  exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg (X ω - Y ω)]⟩

theorem eLpNorm_two_toReal_sq {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ a, f a ^ 2 ∂μ := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ ∫ a, ‖f a‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg fun a => by positivity
  rw [h]
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

/-- `L²` control from a second-moment bound. -/
theorem eLpNorm_two_le_of_integral_sq [IsFiniteMeasure μ] {f : Ω → ℝ} {e : ℝ}
    (hfm : Measurable f) (he : 0 ≤ e) (hfi : Integrable (fun a => f a ^ 2) μ)
    (h : ∫ a, f a ^ 2 ∂μ ≤ e ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal e := by
  have hmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr hfi
  have hfin : eLpNorm f 2 μ ≠ ∞ := hmem.eLpNorm_ne_top
  have hsq := eLpNorm_two_toReal_sq hmem
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f 2 μ)]

/-- Weighted finite sums in `L^q`. -/
theorem eLpNorm_finset_wsum_le {κ : Type*} (s : Finset κ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (X : κ → Ω → ℝ) {a : κ → ℝ} (ha : ∀ k, 0 ≤ a k)
    (hX : ∀ k ∈ s, eLpNorm (X k) q μ ≤ ENNReal.ofReal (a k)) :
    eLpNorm (fun x => ∑ k ∈ s, w k * X k x) q μ ≤
      ENNReal.ofReal (∑ k ∈ s, w k * a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have h1 := ih (fun j hj => hX j (Finset.mem_insert_of_mem hj))
    have h2 := eLpNorm_lincomb_le (μ := μ) hq (X := X k)
      (Y := fun x => ∑ j ∈ s, w j * X j x) (α := w k) (β := 1) (a := a k)
      (c := ∑ j ∈ s, w j * a j) (hw k) zero_le_one (ha k)
      (Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (ha j))
      (hX k (Finset.mem_insert_self k s)) h1
    simp only [one_mul] at h2
    have e : (fun x => ∑ j ∈ insert k s, w j * X j x) =
        fun x => w k * X k x + ∑ j ∈ s, w j * X j x := by
      funext x; rw [Finset.sum_insert hk]
    rw [e, Finset.sum_insert hk]
    exact h2

end Basic

section Consumer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses of the one-load consumer, in abstract form. Each field is a
pathwise inequality of the smooth-feedback estimate or an annealed bound that
is discharged separately from the actual OLD law. -/
structure ConsumerHyp (μ : Measure Ω)
    (Gap Ap PK PD RK RD B Rs Th Eh : Ω → ℝ)
    (v ω dn a5 ξ m b ε Om2 dsq c1 : ℝ) : Prop where
  v0 : 0 ≤ v
  w0 : 0 ≤ ω
  dn0 : 0 ≤ dn
  a50 : 0 ≤ a5
  ξ0 : 0 ≤ ξ
  m0 : 0 ≤ m
  b0 : 0 ≤ b
  ε0 : 0 ≤ ε
  c10 : 0 ≤ c1
  c11 : c1 < 1
  Om0 : 0 ≤ Om2
  Om : Om2 ≤ ω * v
  ds0 : 0 ≤ dsq
  ds : dsq ≤ dn ^ 2 * v
  mGap : Measurable Gap
  mPK : Measurable PK
  mPD : Measurable PD
  mRK : Measurable RK
  mRD : Measurable RD
  mB : Measurable B
  mRs : Measurable Rs
  mAp : Measurable Ap
  mTh : Measurable Th
  mEh : Measurable Eh
  nGap : ∀ x, 0 ≤ Gap x
  nAp : ∀ x, 0 ≤ Ap x
  nPK : ∀ x, 0 ≤ PK x
  nPD : ∀ x, 0 ≤ PD x
  nRK : ∀ x, 0 ≤ RK x
  nRD : ∀ x, 0 ≤ RD x
  nB : ∀ x, 0 ≤ B x
  nRs : ∀ x, 0 ≤ Rs x
  nTh : ∀ x, 0 ≤ Th x
  nEh : ∀ x, 0 ≤ Eh x
  p1 : ∀ x, Gap x ≤ Ap x + 2 * Real.sqrt (PK x * RK x) + RK x +
    2 * Real.sqrt (PD x * RD x) + RD x +
    2 * Real.sqrt dsq * (Real.sqrt (B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) +
      Real.sqrt Om2)
  p2 : ∀ x, Gap x ≤ 2 * (Eh x + B x * (Om2 + dsq))
  p4 : ∀ x, B x ≤ b + Rs x
  iAp : Integrable Ap μ
  iPK : Integrable PK μ
  iPD : Integrable PD μ
  iRK : Integrable RK μ
  iRD : Integrable RD μ
  iTh : Integrable Th μ
  eAp : ∫ x, Ap x ∂μ ≤ a5 / 2 * Om2
  ePK : ∫ x, PK x ∂μ ≤ (1 + a5 / 2) * Om2
  ePD : ∫ x, PD x ∂μ ≤ (1 + a5 / 2) * Om2
  eRK : ∫ x, RK x ∂μ ≤ m * dsq
  eRD : ∫ x, RD x ∂μ ≤ b * dsq
  eTh : ∫ x, Th x ∂μ ≤ ξ / 2 * Om2
  qB : eLpNorm B 128 μ ≤ ENNReal.ofReal b
  qRs : eLpNorm Rs 128 μ ≤ ENNReal.ofReal ε
  qPK : eLpNorm PK (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal (m * Om2 / (1 - c1))
  qRK : eLpNorm RK (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal (m * dsq)
  qEh : eLpNorm Eh (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal (m * (Om2 + dsq))

end Consumer

/-- The source's raw energy constant `E_raw`. -/
def eraW (m ω dn c1 : ℝ) : ℝ := m * (Real.sqrt (ω / (1 - c1)) + dn) ^ 2

/-- The source's `Gap_ε`. -/
def gapEps (a5 ω dn m b ε c1 : ℝ) : ℝ :=
  a5 * ω / 2 + 2 * Real.sqrt ((1 + a5 / 2) * ω * (m * dn ^ 2)) + m * dn ^ 2 +
    2 * Real.sqrt ((1 + a5 / 2) * ω * (b * dn ^ 2)) + b * dn ^ 2 +
    2 * dn * (Real.sqrt (b * (Real.sqrt ((1 + a5 / 2) * ω) + Real.sqrt (m * dn ^ 2)) ^ 2 +
      ε * eraW m ω dn c1) + Real.sqrt ω)

/-- The source's `G_raw`. -/
def graW (m ω dn b c1 : ℝ) : ℝ := 2 * (eraW m ω dn c1 + b * (ω + dn ^ 2))

/-- The source's `L`. -/
def consumerL (a5 ξ ω dn m b ε c0 c1 : ℝ) : ℝ :=
  Real.sqrt (ξ * ω / 2) + Real.sqrt (b * (m * dn ^ 2)) +
    Real.sqrt (b * gapEps a5 ω dn m b ε c1 + ε * graW m ω dn b c1) +
    (1 + c0 * b) * dn

theorem consumer_real_final {v dn δ Os I W w : ℝ} (hv : 0 ≤ v) (hdn : 0 ≤ dn)
    (hδ0 : 0 ≤ δ) (hI0 : 0 ≤ I) (hOs0 : 0 ≤ Os)
    (hδ : δ ≤ dn * Real.sqrt v) (hOs : Os ≤ Real.sqrt w * Real.sqrt v)
    (hI : I ≤ Real.sqrt v * Real.sqrt W) :
    2 * δ * (I + Os) ≤ v * (2 * dn * (Real.sqrt W + Real.sqrt w)) := by
  have hsq := Real.sq_sqrt hv
  have hsv := Real.sqrt_nonneg v
  calc 2 * δ * (I + Os)
      ≤ 2 * (dn * Real.sqrt v) * (Real.sqrt v * Real.sqrt W + Real.sqrt w * Real.sqrt v) :=
        mul_le_mul (by linarith) (add_le_add hI hOs) (by linarith) (by positivity)
    _ = (Real.sqrt v) ^ 2 * (2 * dn * (Real.sqrt W + Real.sqrt w)) := by ring
    _ = _ := by rw [hsq]

section Consumer2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Gap Ap PK PD RK RD B Rs Th Eh : Ω → ℝ}
  {v ω dn a5 ξ m b ε Om2 dsq c1 : ℝ}

theorem consumer_Eb (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) :
    Integrable (fun x => (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) μ ∧
    (∫ x, (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 ∂μ) ≤
      v * (Real.sqrt ((1 + a5 / 2) * ω) + Real.sqrt (m * dn ^ 2)) ^ 2 ∧
    eLpNorm (fun x => (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2)
        (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal (v * eraW m ω dn c1) := by
  obtain ⟨hint, hI⟩ := integral_sqrt_add_sq_le H.mPK H.mRK H.nPK H.nRK H.iPK H.iRK
  have hv := H.v0
  refine ⟨hint, ?_, ?_⟩
  · refine hI.trans ?_
    have h1 : Real.sqrt (∫ x, PK x ∂μ) ≤ Real.sqrt ((1 + a5 / 2) * ω * v) :=
      Real.sqrt_le_sqrt (H.ePK.trans (by
        have := H.a50; have := H.w0; nlinarith [H.Om, H.Om0]))
    have h2 : Real.sqrt (∫ x, RK x ∂μ) ≤ Real.sqrt (m * dn ^ 2 * v) :=
      Real.sqrt_le_sqrt (H.eRK.trans (by
        have := H.m0; nlinarith [H.ds, H.ds0]))
    have h3 : Real.sqrt ((1 + a5 / 2) * ω * v) = Real.sqrt ((1 + a5 / 2) * ω) * Real.sqrt v :=
      Real.sqrt_mul (by have := H.a50; have := H.w0; positivity) v
    have h4 : Real.sqrt (m * dn ^ 2 * v) = Real.sqrt (m * dn ^ 2) * Real.sqrt v :=
      Real.sqrt_mul (by have := H.m0; positivity) v
    calc (Real.sqrt (∫ x, PK x ∂μ) + Real.sqrt (∫ x, RK x ∂μ)) ^ 2
        ≤ (Real.sqrt ((1 + a5 / 2) * ω) * Real.sqrt v + Real.sqrt (m * dn ^ 2) *
            Real.sqrt v) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          rw [← h3, ← h4]; exact add_le_add h1 h2
      _ = v * (Real.sqrt ((1 + a5 / 2) * ω) + Real.sqrt (m * dn ^ 2)) ^ 2 := by
          have := Real.sq_sqrt hv
          nlinarith [this]
  · have hq := eLpNorm_Eb_le (μ := μ) (q := ENNReal.ofReal (128 / 127))
      (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
      H.mPK H.mRK H.nPK H.nRK
      (a := m * Om2 / (1 - c1)) (c := m * dsq)
      (div_nonneg (mul_nonneg H.m0 H.Om0) (by linarith [H.c11]))
      (mul_nonneg H.m0 H.ds0) H.qPK H.qRK
    refine hq.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold eraW
    have h1 : Real.sqrt (m * Om2 / (1 - c1)) ≤
        Real.sqrt (m * (ω / (1 - c1))) * Real.sqrt v := by
      rw [← Real.sqrt_mul (by have := H.m0; have := H.w0
                              have : 0 < 1 - c1 := by linarith [H.c11]
                              positivity)]
      apply Real.sqrt_le_sqrt
      have h1c : 0 < 1 - c1 := by linarith [H.c11]
      have := H.m0
      rw [div_le_iff₀ h1c]
      have : m * (ω / (1 - c1)) * v * (1 - c1) = m * (ω * v) := by field_simp
      nlinarith [H.Om, H.m0]
    have h2 : Real.sqrt (m * dsq) ≤ Real.sqrt m * dn * Real.sqrt v := by
      have h := Real.sqrt_le_sqrt (show m * dsq ≤ m * dn ^ 2 * v by
        have := H.m0; nlinarith [H.ds])
      have e : Real.sqrt (m * dn ^ 2 * v) = Real.sqrt m * dn * Real.sqrt v := by
        rw [Real.sqrt_mul (mul_nonneg H.m0 (sq_nonneg dn)) v,
          Real.sqrt_mul H.m0, Real.sqrt_sq H.dn0]
      rw [e] at h
      exact h
    have hsm : Real.sqrt (m * (ω / (1 - c1))) =
        Real.sqrt m * Real.sqrt (ω / (1 - c1)) := Real.sqrt_mul H.m0 _
    have hs0 := Real.sqrt_nonneg m
    have hs1 := Real.sqrt_nonneg v
    have hs2 := Real.sqrt_nonneg (ω / (1 - c1))
    calc (Real.sqrt (m * Om2 / (1 - c1)) + Real.sqrt (m * dsq)) ^ 2
        ≤ (Real.sqrt m * Real.sqrt (ω / (1 - c1)) * Real.sqrt v +
            Real.sqrt m * dn * Real.sqrt v) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          rw [hsm] at h1
          exact add_le_add h1 h2
      _ = (Real.sqrt m * Real.sqrt v) ^ 2 * (Real.sqrt (ω / (1 - c1)) + dn) ^ 2 := by ring
      _ = v * (m * (Real.sqrt (ω / (1 - c1)) + dn) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hv, Real.sq_sqrt H.m0]; ring

theorem consumer_integrable_B (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) : Integrable B μ := by
  have hmem : MemLp B 128 μ := memLp_iff.mpr (H.qB.trans_lt ENNReal.ofReal_lt_top)
  exact hmem.integrable (by norm_num)

theorem consumer_BEb (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) :
    Integrable (fun x => B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) μ ∧
    (∫ x, B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 ∂μ) ≤
      v * (b * (Real.sqrt ((1 + a5 / 2) * ω) + Real.sqrt (m * dn ^ 2)) ^ 2 +
        ε * eraW m ω dn c1) := by
  obtain ⟨hEbI, hEbE, hEbq⟩ := consumer_Eb H
  have hEm : Measurable (fun x => (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) :=
    (H.mPK.sqrt.add H.mRK.sqrt).pow_const 2
  have hE0 : ∀ x, 0 ≤ (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 := fun x => sq_nonneg _
  have hv := H.v0
  have hEraw : 0 ≤ v * eraW m ω dn c1 := by
    unfold eraW
    have h1c : 0 < 1 - c1 := by linarith [H.c11]
    have := H.m0; have := H.w0
    positivity
  have hRsE := integrable_mul_128 (μ := μ) H.mRs hEm H.qRs hEbq
  have hRsEle := integral_mul_le_128 (μ := μ) H.mRs hEm H.nRs hE0 H.ε0 hEraw H.qRs hEbq
  have hbE : Integrable (fun x => b * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) μ :=
    hEbI.const_mul b
  have hsum : Integrable (fun x => b * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 +
      Rs x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) μ := hbE.add hRsE
  have hle (x : Ω) : B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 ≤
      b * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 +
        Rs x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 := by
    have := H.p4 x
    nlinarith [hE0 x]
  have hBEm : Measurable (fun x => B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) :=
    H.mB.mul hEm
  have hBEi : Integrable (fun x => B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) μ := by
    refine hsum.mono' hBEm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (H.nB x) (hE0 x))]
    exact hle x
  refine ⟨hBEi, ?_⟩
  calc ∫ x, B x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 ∂μ
      ≤ ∫ x, (b * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 +
          Rs x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2) ∂μ :=
        integral_mono hBEi hsum hle
    _ = b * ∫ x, (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 ∂μ +
          ∫ x, Rs x * (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2 ∂μ := by
        rw [integral_add hbE hRsE, integral_const_mul]
    _ ≤ b * (v * (Real.sqrt ((1 + a5 / 2) * ω) + Real.sqrt (m * dn ^ 2)) ^ 2) +
          ε * (v * eraW m ω dn c1) :=
        add_le_add (mul_le_mul_of_nonneg_left hEbE H.b0) hRsEle
    _ = _ := by ring

theorem consumer_gap (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) :
    ∫ x, Gap x ∂μ ≤ v * gapEps a5 ω dn m b ε c1 := by
  obtain ⟨hBEi, hBEe⟩ := consumer_BEb H
  have hv := H.v0
  let Eb : Ω → ℝ := fun x => (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2
  have hBI := consumer_integrable_B H
  have hBEm : Measurable (fun x => B x * Eb x) :=
    H.mB.mul ((H.mPK.sqrt.add H.mRK.sqrt).pow_const 2)
  have hBE0 : ∀ x, 0 ≤ B x * Eb x := fun x => mul_nonneg (H.nB x) (sq_nonneg _)
  have iSBE : Integrable (fun x => Real.sqrt (B x * Eb x)) μ := by
    refine Integrable.mono' ((hBEi.add (integrable_const (1 : ℝ))))
      hBEm.sqrt.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h0 := hBE0 x
    show Real.sqrt (B x * Eb x) ≤ B x * Eb x + 1
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have iS1 := integrable_sqrt_mul (μ := μ) H.mPK H.mRK H.nPK H.nRK H.iPK H.iRK
  have iS2 := integrable_sqrt_mul (μ := μ) H.mPD H.mRD H.nPD H.nRD H.iPD H.iRD
  let δ : ℝ := Real.sqrt dsq
  let Os : ℝ := Real.sqrt Om2
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hOs0 : 0 ≤ Os := Real.sqrt_nonneg _
  have i6 : Integrable (fun x => 2 * δ * (Real.sqrt (B x * Eb x) + Os)) μ :=
    (iSBE.add (integrable_const Os)).const_mul (2 * δ)
  have iG : Integrable (fun x => Ap x + 2 * Real.sqrt (PK x * RK x) + RK x +
      2 * Real.sqrt (PD x * RD x) + RD x + 2 * δ * (Real.sqrt (B x * Eb x) + Os)) μ :=
    ((((H.iAp.add (iS1.const_mul 2)).add H.iRK).add (iS2.const_mul 2)).add H.iRD).add i6
  have hle : ∀ x, Gap x ≤ Ap x + 2 * Real.sqrt (PK x * RK x) + RK x +
      2 * Real.sqrt (PD x * RD x) + RD x + 2 * δ * (Real.sqrt (B x * Eb x) + Os) :=
    fun x => H.p1 x
  have step1 : ∫ x, Gap x ∂μ ≤ ∫ x, (Ap x + 2 * Real.sqrt (PK x * RK x) + RK x +
      2 * Real.sqrt (PD x * RD x) + RD x + 2 * δ * (Real.sqrt (B x * Eb x) + Os)) ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall H.nGap) iG
      (Filter.Eventually.of_forall hle)
  refine step1.trans ?_
  rw [integral_add6 H.iAp (iS1.const_mul 2) H.iRK (iS2.const_mul 2) H.iRD i6]
  rw [integral_const_mul, integral_const_mul]
  have cs1 := integral_sqrt_mul_le (μ := μ) H.mPK H.mRK H.nPK H.nRK H.iPK H.iRK
  have cs2 := integral_sqrt_mul_le (μ := μ) H.mPD H.mRD H.nPD H.nRD H.iPD H.iRD
  have hP0 : 0 ≤ (1 + a5 / 2) := by have := H.a50; positivity
  have hIPK0 : 0 ≤ ∫ x, PK x ∂μ := integral_nonneg (fun x => H.nPK x)
  have hIPD0 : 0 ≤ ∫ x, PD x ∂μ := integral_nonneg (fun x => H.nPD x)
  have hIRK0 : 0 ≤ ∫ x, RK x ∂μ := integral_nonneg (fun x => H.nRK x)
  have hIRD0 : 0 ≤ ∫ x, RD x ∂μ := integral_nonneg (fun x => H.nRD x)
  have hPv : (1 + a5 / 2) * Om2 ≤ (1 + a5 / 2) * ω * v := by
    have := H.Om; nlinarith
  have hRv : m * dsq ≤ m * dn ^ 2 * v := by
    have := H.m0; have := H.ds; nlinarith
  have hRDv : b * dsq ≤ b * dn ^ 2 * v := by
    have := H.b0; have := H.ds; nlinarith
  have hsqK : Real.sqrt ((∫ x, PK x ∂μ) * ∫ x, RK x ∂μ) ≤
      v * Real.sqrt ((1 + a5 / 2) * ω * (m * dn ^ 2)) := by
    calc _ ≤ Real.sqrt (((1 + a5 / 2) * ω * v) * (m * dn ^ 2 * v)) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul (H.ePK.trans hPv) (H.eRK.trans hRv) hIRK0 (by
            have := H.w0; positivity)
      _ = v * Real.sqrt ((1 + a5 / 2) * ω * (m * dn ^ 2)) := by
          have : ((1 + a5 / 2) * ω * v) * (m * dn ^ 2 * v) =
              v ^ 2 * ((1 + a5 / 2) * ω * (m * dn ^ 2)) := by ring
          rw [this, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
  have hsqD : Real.sqrt ((∫ x, PD x ∂μ) * ∫ x, RD x ∂μ) ≤
      v * Real.sqrt ((1 + a5 / 2) * ω * (b * dn ^ 2)) := by
    calc _ ≤ Real.sqrt (((1 + a5 / 2) * ω * v) * (b * dn ^ 2 * v)) := by
          apply Real.sqrt_le_sqrt
          exact mul_le_mul (H.ePD.trans hPv) (H.eRD.trans hRDv) hIRD0 (by
            have := H.w0; positivity)
      _ = v * Real.sqrt ((1 + a5 / 2) * ω * (b * dn ^ 2)) := by
          have : ((1 + a5 / 2) * ω * v) * (b * dn ^ 2 * v) =
              v ^ 2 * ((1 + a5 / 2) * ω * (b * dn ^ 2)) := by ring
          rw [this, Real.sqrt_mul (sq_nonneg v), Real.sqrt_sq hv]
  have jen := integral_sqrt_le (μ := μ) hBEm hBE0 hBEi
  have hW0 : 0 ≤ v * (b * (Real.sqrt ((1 + a5 / 2) * ω) + Real.sqrt (m * dn ^ 2)) ^ 2 +
      ε * eraW m ω dn c1) := by
    have h1c : 0 < 1 - c1 := by linarith [H.c11]
    unfold eraW
    have := H.m0; have := H.w0; have := H.b0; have := H.ε0
    positivity
  have hsqB : ∫ x, Real.sqrt (B x * Eb x) ∂μ ≤
      Real.sqrt v * Real.sqrt (b * (Real.sqrt ((1 + a5 / 2) * ω) +
        Real.sqrt (m * dn ^ 2)) ^ 2 + ε * eraW m ω dn c1) := by
    refine jen.trans ?_
    rw [← Real.sqrt_mul hv]
    exact Real.sqrt_le_sqrt hBEe
  have hδ : δ ≤ dn * Real.sqrt v := by
    have h := Real.sqrt_le_sqrt H.ds
    rw [Real.sqrt_mul (sq_nonneg dn), Real.sqrt_sq H.dn0] at h
    exact h
  have hOs : Os ≤ Real.sqrt ω * Real.sqrt v := by
    have h := Real.sqrt_le_sqrt H.Om
    rw [Real.sqrt_mul H.w0] at h
    exact h
  have hint6 : ∫ x, 2 * δ * (Real.sqrt (B x * Eb x) + Os) ∂μ =
      2 * δ * ((∫ x, Real.sqrt (B x * Eb x) ∂μ) + Os) := by
    rw [integral_const_mul, integral_add iSBE (integrable_const Os)]
    simp
  rw [hint6]
  have hfinal : 2 * δ * ((∫ x, Real.sqrt (B x * Eb x) ∂μ) + Os) ≤
      v * (2 * dn * (Real.sqrt (b * (Real.sqrt ((1 + a5 / 2) * ω) +
        Real.sqrt (m * dn ^ 2)) ^ 2 + ε * eraW m ω dn c1) + Real.sqrt ω)) :=
    consumer_real_final hv H.dn0 hδ0 (integral_nonneg (fun x => Real.sqrt_nonneg _))
      hOs0 hδ hOs hsqB
  have e1 : a5 / 2 * Om2 ≤ v * (a5 * ω / 2) := by
    have := H.a50; nlinarith [H.Om]
  have e3 : m * dsq ≤ v * (m * dn ^ 2) := by nlinarith [hRv]
  have e5 : b * dsq ≤ v * (b * dn ^ 2) := by nlinarith [hRDv]
  have hex : v * gapEps a5 ω dn m b ε c1 =
      v * (a5 * ω / 2) + 2 * (v * Real.sqrt ((1 + a5 / 2) * ω * (m * dn ^ 2))) +
        v * (m * dn ^ 2) + 2 * (v * Real.sqrt ((1 + a5 / 2) * ω * (b * dn ^ 2))) +
        v * (b * dn ^ 2) +
        v * (2 * dn * (Real.sqrt (b * (Real.sqrt ((1 + a5 / 2) * ω) +
          Real.sqrt (m * dn ^ 2)) ^ 2 + ε * eraW m ω dn c1) + Real.sqrt ω)) := by
    unfold gapEps; ring
  rw [hex]
  linarith [H.eAp, e1, e3, e5, hsqK, hsqD, hfinal, H.eRK, H.eRD, cs1, cs2]

theorem consumer_gap_integrable (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) : Integrable Gap μ := by
  obtain ⟨hBEi, hBEe⟩ := consumer_BEb H
  let Eb : Ω → ℝ := fun x => (Real.sqrt (PK x) + Real.sqrt (RK x)) ^ 2
  have hBEm : Measurable (fun x => B x * Eb x) :=
    H.mB.mul ((H.mPK.sqrt.add H.mRK.sqrt).pow_const 2)
  have hBE0 : ∀ x, 0 ≤ B x * Eb x := fun x => mul_nonneg (H.nB x) (sq_nonneg _)
  have iSBE : Integrable (fun x => Real.sqrt (B x * Eb x)) μ := by
    refine Integrable.mono' ((hBEi.add (integrable_const (1 : ℝ))))
      hBEm.sqrt.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have h0 := hBE0 x
    show Real.sqrt (B x * Eb x) ≤ B x * Eb x + 1
    exact Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have iS1 := integrable_sqrt_mul (μ := μ) H.mPK H.mRK H.nPK H.nRK H.iPK H.iRK
  have iS2 := integrable_sqrt_mul (μ := μ) H.mPD H.mRD H.nPD H.nRD H.iPD H.iRD
  let δ : ℝ := Real.sqrt dsq
  let Os : ℝ := Real.sqrt Om2
  have i6 : Integrable (fun x => 2 * δ * (Real.sqrt (B x * Eb x) + Os)) μ :=
    (iSBE.add (integrable_const Os)).const_mul (2 * δ)
  have iG : Integrable (fun x => Ap x + 2 * Real.sqrt (PK x * RK x) + RK x +
      2 * Real.sqrt (PD x * RD x) + RD x + 2 * δ * (Real.sqrt (B x * Eb x) + Os)) μ :=
    ((((H.iAp.add (iS1.const_mul 2)).add H.iRK).add (iS2.const_mul 2)).add H.iRD).add i6
  refine iG.mono' H.mGap.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (H.nGap x)]
  exact H.p1 x

theorem consumer_gap_q (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) :
    eLpNorm Gap (ENNReal.ofReal (128 / 127)) μ ≤
      ENNReal.ofReal (v * graW m ω dn b c1) := by
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (128 / 127) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hqB : eLpNorm B (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal b := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le ?_).trans H.qB
    have : ENNReal.ofReal (128 / 127) ≤ ENNReal.ofReal 128 :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    simpa using this
  have hOm : 0 ≤ Om2 + dsq := add_nonneg H.Om0 H.ds0
  have hlin := eLpNorm_lincomb_le (μ := μ) hq (X := Eh) (Y := B) (α := 2)
    (β := 2 * (Om2 + dsq)) (a := m * (Om2 + dsq)) (c := b) (by norm_num)
    (by positivity) (mul_nonneg H.m0 hOm) H.b0 H.qEh hqB
  have hmono : eLpNorm Gap (ENNReal.ofReal (128 / 127)) μ ≤
      eLpNorm (fun x => 2 * Eh x + 2 * (Om2 + dsq) * B x)
        (ENNReal.ofReal (128 / 127)) μ := by
    apply eLpNorm_mono_real H.mGap.aestronglyMeasurable
    intro x
    rw [Real.norm_of_nonneg (H.nGap x)]
    have := H.p2 x
    nlinarith
  refine hmono.trans (hlin.trans (ENNReal.ofReal_le_ofReal ?_))
  unfold graW eraW
  have hv := H.v0
  have h1c : 0 < 1 - c1 := by linarith [H.c11]
  have hs : ω ≤ (Real.sqrt (ω / (1 - c1))) ^ 2 := by
    rw [Real.sq_sqrt (by have := H.w0; positivity)]
    have := H.w0
    rw [le_div_iff₀ h1c]
    nlinarith [H.c10]
  have hE : ω + dn ^ 2 ≤ (Real.sqrt (ω / (1 - c1)) + dn) ^ 2 := by
    have := Real.sqrt_nonneg (ω / (1 - c1))
    nlinarith [H.dn0]
  have hOd : Om2 + dsq ≤ v * (ω + dn ^ 2) := by nlinarith [H.Om, H.ds]
  have hm := H.m0
  have hb := H.b0
  nlinarith [mul_le_mul_of_nonneg_left hOd hm, mul_le_mul_of_nonneg_left hOd hb,
    mul_le_mul_of_nonneg_left hE hm, mul_nonneg hv hm,
    mul_le_mul_of_nonneg_left hE (mul_nonneg hv hm)]

theorem consumer_BGap (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) :
    Integrable (fun x => B x * Gap x) μ ∧
    ∫ x, B x * Gap x ∂μ ≤ v * (b * gapEps a5 ω dn m b ε c1 + ε * graW m ω dn b c1) := by
  have hGi := consumer_gap_integrable H
  have hGq := consumer_gap_q H
  have hv := H.v0
  have hGraw : 0 ≤ v * graW m ω dn b c1 := by
    unfold graW eraW
    have h1c : 0 < 1 - c1 := by linarith [H.c11]
    have := H.m0; have := H.w0; have := H.b0
    positivity
  have hRG := integrable_mul_128 (μ := μ) H.mRs H.mGap H.qRs hGq
  have hRGle := integral_mul_le_128 (μ := μ) H.mRs H.mGap H.nRs H.nGap H.ε0 hGraw
    H.qRs hGq
  have hbG : Integrable (fun x => b * Gap x + Rs x * Gap x) μ := (hGi.const_mul b).add hRG
  have hle (x : Ω) : B x * Gap x ≤ b * Gap x + Rs x * Gap x := by
    have := H.p4 x
    nlinarith [H.nGap x]
  have hBGm : Measurable (fun x => B x * Gap x) := H.mB.mul H.mGap
  have hBGi : Integrable (fun x => B x * Gap x) μ := by
    refine hbG.mono' hBGm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (H.nB x) (H.nGap x))]
    exact hle x
  refine ⟨hBGi, ?_⟩
  have hG := consumer_gap H
  calc ∫ x, B x * Gap x ∂μ ≤ ∫ x, (b * Gap x + Rs x * Gap x) ∂μ :=
        integral_mono hBGi hbG hle
    _ = b * ∫ x, Gap x ∂μ + ∫ x, Rs x * Gap x ∂μ := by
        rw [integral_add (hGi.const_mul b) hRG, integral_const_mul]
    _ ≤ b * (v * gapEps a5 ω dn m b ε c1) + ε * (v * graW m ω dn b c1) :=
        add_le_add (mul_le_mul_of_nonneg_left hG H.b0) hRGle
    _ = _ := by ring

theorem consumer_Fw (H : ConsumerHyp μ Gap Ap PK PD RK RD B Rs Th Eh
    v ω dn a5 ξ m b ε Om2 dsq c1) {Fw2 : Ω → ℝ} {c0 : ℝ} (hc0 : 0 ≤ c0)
    (mFw : Measurable Fw2) (nFw : ∀ x, 0 ≤ Fw2 x)
    (p3 : ∀ x, Real.sqrt (Fw2 x) ≤ Real.sqrt (Th x) + Real.sqrt (B x * RK x) +
      Real.sqrt (B x * Gap x) + (1 + c0 * B x) * Real.sqrt dsq) :
    ∫ x, Fw2 x ∂μ ≤ v * (consumerL a5 ξ ω dn m b ε c0 c1) ^ 2 := by
  have hv := H.v0
  have hsv := Real.sqrt_nonneg v
  have h2 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  -- the four summands
  obtain ⟨hBGi, hBGe⟩ := consumer_BGap H
  have hBRKi := integrable_mul_128 (μ := μ) H.mB H.mRK H.qB H.qRK
  have hBRKe := integral_mul_le_128 (μ := μ) H.mB H.mRK H.nB H.nRK H.b0
    (mul_nonneg H.m0 H.ds0) H.qB H.qRK
  have e1 : eLpNorm (fun x => Real.sqrt (Th x)) 2 μ ≤
      ENNReal.ofReal (Real.sqrt v * Real.sqrt (ξ * ω / 2)) := by
    apply eLpNorm_two_le_of_integral_sq H.mTh.sqrt (by positivity)
    · refine H.iTh.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [Real.sq_sqrt (H.nTh x)]
    · have : ∫ x, Real.sqrt (Th x) ^ 2 ∂μ = ∫ x, Th x ∂μ := by
        congr 1; funext x; exact Real.sq_sqrt (H.nTh x)
      rw [this, mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (by have := H.ξ0; have := H.w0; positivity)]
      refine H.eTh.trans ?_
      have := H.ξ0
      nlinarith [H.Om]
  have e2 : eLpNorm (fun x => Real.sqrt (B x * RK x)) 2 μ ≤
      ENNReal.ofReal (Real.sqrt v * Real.sqrt (b * (m * dn ^ 2))) := by
    have hm2 : Measurable (fun x => Real.sqrt (B x * RK x)) := (H.mB.mul H.mRK).sqrt
    apply eLpNorm_two_le_of_integral_sq hm2 (by positivity)
    · refine hBRKi.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [Real.sq_sqrt (mul_nonneg (H.nB x) (H.nRK x))]
    · have : ∫ x, Real.sqrt (B x * RK x) ^ 2 ∂μ = ∫ x, B x * RK x ∂μ := by
        congr 1; funext x; exact Real.sq_sqrt (mul_nonneg (H.nB x) (H.nRK x))
      rw [this, mul_pow, Real.sq_sqrt hv, Real.sq_sqrt (by have := H.b0; have := H.m0; positivity)]
      refine hBRKe.trans ?_
      have := H.b0; have := H.m0
      nlinarith [H.ds, mul_nonneg H.b0 H.m0]
  have e3 : eLpNorm (fun x => Real.sqrt (B x * Gap x)) 2 μ ≤
      ENNReal.ofReal (Real.sqrt v * Real.sqrt (b * gapEps a5 ω dn m b ε c1 +
        ε * graW m ω dn b c1)) := by
    have hm3 : Measurable (fun x => Real.sqrt (B x * Gap x)) := (H.mB.mul H.mGap).sqrt
    apply eLpNorm_two_le_of_integral_sq hm3 (by
      have : 0 ≤ b * gapEps a5 ω dn m b ε c1 + ε * graW m ω dn b c1 := by
        unfold gapEps graW eraW
        have h1c : 0 < 1 - c1 := by linarith [H.c11]
        have := H.b0; have := H.ε0; have := H.m0; have := H.w0; have := H.a50
        have := H.dn0
        positivity
      positivity)
    · refine hBGi.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [Real.sq_sqrt (mul_nonneg (H.nB x) (H.nGap x))]
    · have : ∫ x, Real.sqrt (B x * Gap x) ^ 2 ∂μ = ∫ x, B x * Gap x ∂μ := by
        congr 1; funext x; exact Real.sq_sqrt (mul_nonneg (H.nB x) (H.nGap x))
      have hnn : 0 ≤ b * gapEps a5 ω dn m b ε c1 + ε * graW m ω dn b c1 := by
        unfold gapEps graW eraW
        have h1c : 0 < 1 - c1 := by linarith [H.c11]
        have := H.b0; have := H.ε0; have := H.m0; have := H.w0; have := H.a50
        have := H.dn0
        positivity
      rw [this, mul_pow, Real.sq_sqrt hv, Real.sq_sqrt hnn]
      exact hBGe
  have hqB2 : eLpNorm B 2 μ ≤ ENNReal.ofReal b := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le ?_).trans H.qB
    norm_num
  have hone : eLpNorm (fun _ : Ω => (1 : ℝ)) 2 μ ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero μ)]
    simp
  have e4 := eLpNorm_lincomb_le (μ := μ) h2 (X := fun _ : Ω => (1 : ℝ)) (Y := B)
    (α := Real.sqrt dsq) (β := Real.sqrt dsq * c0) (a := 1) (c := b)
    (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hc0) zero_le_one H.b0 hone hqB2
  have hδ : Real.sqrt dsq ≤ dn * Real.sqrt v := by
    have h := Real.sqrt_le_sqrt H.ds
    rw [Real.sqrt_mul (sq_nonneg dn), Real.sqrt_sq H.dn0] at h
    exact h
  let F : Ω → ℝ := fun x => Real.sqrt (Fw2 x)
  have hFm : Measurable F := mFw.sqrt
  let f1 : Ω → ℝ := fun x => Real.sqrt (Th x)
  let f2 : Ω → ℝ := fun x => Real.sqrt (B x * RK x)
  let f3 : Ω → ℝ := fun x => Real.sqrt (B x * Gap x)
  let f4 : Ω → ℝ := fun x => (1 + c0 * B x) * Real.sqrt dsq
  have hF : eLpNorm F 2 μ ≤ eLpNorm (f1 + f2 + f3 + f4) 2 μ := by
    apply eLpNorm_mono_real hFm.aestronglyMeasurable
    intro x
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact p3 x
  have e4' : eLpNorm f4 2 μ ≤ ENNReal.ofReal (Real.sqrt dsq * 1 + Real.sqrt dsq * c0 * b) := by
    have : f4 = fun ω => Real.sqrt dsq * (fun _ : Ω => (1 : ℝ)) ω +
        Real.sqrt dsq * c0 * B ω := by
      funext x; simp only [f4]; ring
    rw [this]; exact e4
  have hsum : eLpNorm (f1 + f2 + f3 + f4) 2 μ ≤
      ENNReal.ofReal (Real.sqrt v * Real.sqrt (ξ * ω / 2)) +
      ENNReal.ofReal (Real.sqrt v * Real.sqrt (b * (m * dn ^ 2))) +
      ENNReal.ofReal (Real.sqrt v * Real.sqrt (b * gapEps a5 ω dn m b ε c1 +
        ε * graW m ω dn b c1)) +
      ENNReal.ofReal (Real.sqrt dsq * 1 + Real.sqrt dsq * c0 * b) := by
    refine (eLpNorm_add_le h2).trans (add_le_add ?_ e4')
    refine (eLpNorm_add_le h2).trans (add_le_add ?_ e3)
    exact (eLpNorm_add_le h2).trans (add_le_add e1 e2)
  have hL : 0 ≤ Real.sqrt v * consumerL a5 ξ ω dn m b ε c0 c1 := by
    unfold consumerL
    have := H.dn0; have := H.b0
    positivity
  have hbound : eLpNorm F 2 μ ≤ ENNReal.ofReal (Real.sqrt v *
      consumerL a5 ξ ω dn m b ε c0 c1) := by
    refine hF.trans (hsum.trans ?_)
    have hb0 := H.b0
    have hm0 := H.m0
    have hε0 := H.ε0
    have hgn : 0 ≤ b * gapEps a5 ω dn m b ε c1 + ε * graW m ω dn b c1 := by
      unfold gapEps graW eraW
      have h1c : 0 < 1 - c1 := by linarith [H.c11]
      have := H.w0; have := H.a50; have := H.dn0
      positivity
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold consumerL
    have hd : Real.sqrt dsq * 1 + Real.sqrt dsq * c0 * b ≤
        Real.sqrt v * ((1 + c0 * b) * dn) := by
      have := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 1 + c0 * b)
      nlinarith [this, hδ, mul_nonneg hc0 H.b0, Real.sqrt_nonneg dsq]
    nlinarith [hd]
  have hmem : MemLp F 2 μ := memLp_iff.mpr (hbound.trans_lt ENNReal.ofReal_lt_top)
  have hsq := eLpNorm_two_toReal_sq hmem
  have hle : (eLpNorm F 2 μ).toReal ≤ Real.sqrt v * consumerL a5 ξ ω dn m b ε c0 c1 :=
    ENNReal.toReal_le_of_le_ofReal hL hbound
  have hFsq : ∫ x, Fw2 x ∂μ = ∫ x, F x ^ 2 ∂μ := by
    congr 1; funext x; exact (Real.sq_sqrt (nFw x)).symm
  rw [hFsq, ← hsq]
  calc (eLpNorm F 2 μ).toReal ^ 2 ≤ (Real.sqrt v * consumerL a5 ξ ω dn m b ε c0 c1) ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
    _ = v * (consumerL a5 ξ ω dn m b ε c0 c1) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hv]

end Consumer2

section Agg

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem eLpNorm_exponent_down {f : Ω → ℝ} {p q : ℝ≥0∞} (h : p ≤ q) :
    eLpNorm f p μ ≤ eLpNorm f q μ :=
  eLpNorm_le_eLpNorm_of_exponent_le h

/-- Aggregation of cellwise history bounds: a measurable nonnegative quantity
dominated by a weighted average of nonnegative `L²`-bounded cell histories is
integrable, with `L¹` and `L^(128/127)` bounds. -/
theorem agg_bounds {ι κ : Type*} [Fintype κ] (S : Finset ι) (cinv : ℝ) (hc : 0 ≤ cinv)
    (c : ι → κ → ℝ) (hc0 : ∀ i k, 0 ≤ c i k) (Mf : κ → Ω → ℝ) (hM0 : ∀ k x, 0 ≤ Mf k x)
    {m : ℝ} (hm0 : 0 ≤ m) (hM2 : ∀ k, eLpNorm (Mf k) 2 μ ≤ ENNReal.ofReal m)
    (Z : Ω → ℝ) (hZm : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x)
    (hZle : ∀ x, Z x ≤ ∑ i ∈ S, cinv * ∑ k, c i k * Mf k x) :
    Integrable Z μ ∧
    (∫ x, Z x ∂μ) ≤ m * ∑ i ∈ S, cinv * ∑ k, c i k ∧
    eLpNorm Z (ENNReal.ofReal (128 / 127)) μ ≤
      ENNReal.ofReal (m * ∑ i ∈ S, cinv * ∑ k, c i k) := by
  classical
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (128 / 127) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hq2 : ENNReal.ofReal (128 / 127) ≤ 2 := by
    have : ENNReal.ofReal (128 / 127) ≤ ENNReal.ofReal 2 :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    simpa using this
  have hMq (k : κ) : eLpNorm (Mf k) (ENNReal.ofReal (128 / 127)) μ ≤ ENNReal.ofReal m :=
    (eLpNorm_exponent_down hq2).trans (hM2 k)
  have hin (i : ι) : eLpNorm (fun x => ∑ k, c i k * Mf k x) (ENNReal.ofReal (128 / 127)) μ ≤
      ENNReal.ofReal (∑ k, c i k * m) :=
    eLpNorm_finset_wsum_le Finset.univ hq1 (c i) (hc0 i) Mf (a := fun _ => m)
      (fun _ => hm0) (fun k _ => hMq k)
  have hout : eLpNorm (fun x => ∑ i ∈ S, cinv * ∑ k, c i k * Mf k x)
      (ENNReal.ofReal (128 / 127)) μ ≤
      ENNReal.ofReal (∑ i ∈ S, cinv * ∑ k, c i k * m) :=
    eLpNorm_finset_wsum_le S hq1 (fun _ => cinv) (fun _ => hc)
      (fun i x => ∑ k, c i k * Mf k x) (a := fun i => ∑ k, c i k * m)
      (fun i => Finset.sum_nonneg fun k _ => mul_nonneg (hc0 i k) hm0) (fun i _ => hin i)
  have hsumeq : (∑ i ∈ S, cinv * ∑ k, c i k * m) = m * ∑ i ∈ S, cinv * ∑ k, c i k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]; ring
  rw [hsumeq] at hout
  have hY0 : ∀ x, 0 ≤ ∑ i ∈ S, cinv * ∑ k, c i k * Mf k x := fun x =>
    Finset.sum_nonneg fun i _ => mul_nonneg hc (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hc0 i k) (hM0 k x))
  have hZq : eLpNorm Z (ENNReal.ofReal (128 / 127)) μ ≤
      ENNReal.ofReal (m * ∑ i ∈ S, cinv * ∑ k, c i k) := by
    refine (eLpNorm_mono_real hZm.aestronglyMeasurable (fun x => ?_)).trans hout
    rw [Real.norm_of_nonneg (hZ0 x)]
    exact hZle x
  refine ⟨?_, ?_, hZq⟩
  · have hmem : MemLp Z (ENNReal.ofReal (128 / 127)) μ :=
      memLp_iff.mpr (hZq.trans_lt ENNReal.ofReal_lt_top)
    exact hmem.integrable hq1
  · have h1 : eLpNorm Z 1 μ ≤ eLpNorm Z (ENNReal.ofReal (128 / 127)) μ :=
      eLpNorm_exponent_down hq1
    have hint : Integrable Z μ :=
      (memLp_iff.mpr ((h1.trans hZq).trans_lt ENNReal.ofReal_lt_top) :
        MemLp Z 1 μ) |> memLp_one_iff_integrable.mp
    have hnorm : eLpNorm Z 1 μ = ENNReal.ofReal (∫ x, Z x ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      have : ∫⁻ x, ‖Z x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (Z x) ∂μ := by
        congr 1; funext x; rw [Real.enorm_eq_ofReal (hZ0 x)]
      rw [this]
      exact (ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hZ0)).symm
      all_goals exact hZm.aestronglyMeasurable
    have h2 := h1.trans hZq
    rw [hnorm] at h2
    have hnn : 0 ≤ m * ∑ i ∈ S, cinv * ∑ k, c i k :=
      mul_nonneg hm0 (Finset.sum_nonneg fun i _ => mul_nonneg hc
        (Finset.sum_nonneg fun k _ => hc0 i k))
    exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h2

end Agg

end

end ASDExplicitGamma.Scalar
