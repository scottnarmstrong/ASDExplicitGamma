module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Exact centering for nonnegative random variables

This is a separate inequality from Rio's martingale estimate. The hypotheses
`X ≥ 0` and `p ≥ 2` are essential.
-/

@[expose] public section

namespace ASDExplicitGamma.Cold

open MeasureTheory Set
open scoped ENNReal

/-- The scalar inequality underlying CO-EXACT-CENTERING. -/
theorem abs_sub_rpow_le_tangent_remainder {x m p : ℝ}
    (hx : 0 ≤ x) (hm : 0 ≤ m) (hp : 2 ≤ p) :
    |x - m| ^ p ≤ x ^ p - p * m ^ (p - 1) * x + (p - 1) * m ^ p := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hq : 1 ≤ p - 1 := by linarith only [hp]
  have hpow : m ^ (p - 1) * m = m ^ p := by
    have h := Real.rpow_add_one' (y := p - 1) hm (by linarith : p - 1 + 1 ≠ 0)
    simpa only [sub_add_cancel] using h.symm
  by_cases hmx : m ≤ x
  · let f : ℝ → ℝ := fun y => y ^ p - (y - m) ^ p - p * m ^ (p - 1) * y
    have hd (y : ℝ) : HasDerivAt f
        (p * (y ^ (p - 1) - (y - m) ^ (p - 1) - m ^ (p - 1))) y := by
      convert! ((Real.hasDerivAt_rpow_const (x := y) (Or.inr hp1)).sub
        (((hasDerivAt_id y).sub_const m).rpow_const (Or.inr hp1))).sub
        ((hasDerivAt_id y).const_mul (p * m ^ (p - 1))) using 1
      simp only [id_eq, sub_eq_add_neg, add_comm]
      ring
    have hmono : MonotoneOn f (Ici m) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici m)
        (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
      intro y hy
      rw [(hd y).deriv]
      have hmy : m ≤ y := (interior_subset hy)
      have hsum := Real.add_rpow_le_rpow_add hm (sub_nonneg.mpr hmy) hq
      rw [add_sub_cancel] at hsum
      exact mul_nonneg (by linarith only [hp]) (by linarith only [hsum])
    have h := hmono (le_refl m) hmx hmx
    have hzero : (0 : ℝ) ^ p = 0 := Real.zero_rpow (by linarith : p ≠ 0)
    dsimp only [f] at h
    rw [sub_self, hzero, sub_zero] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hmx)]
    have heq : p * m ^ (p - 1) * m = p * m ^ p := by rw [mul_assoc, hpow]
    rw [heq] at h
    linarith only [h]
  · have hxm : x ≤ m := le_of_lt (lt_of_not_ge hmx)
    let f : ℝ → ℝ := fun y => y ^ p - (m - y) ^ p - p * m ^ (p - 1) * y
    have hd (y : ℝ) : HasDerivAt f
        (p * (y ^ (p - 1) + (m - y) ^ (p - 1) - m ^ (p - 1))) y := by
      convert! ((Real.hasDerivAt_rpow_const (x := y) (Or.inr hp1)).sub
        (((hasDerivAt_const y m).sub (hasDerivAt_id y)).rpow_const (Or.inr hp1))).sub
        ((hasDerivAt_id y).const_mul (p * m ^ (p - 1))) using 1
      simp only [id_eq, Pi.sub_apply, sub_eq_add_neg, add_comm]
      ring
    have hanti : AntitoneOn f (Icc 0 m) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 m)
        (fun y _ => (hd y).continuousAt.continuousWithinAt)
        (fun y _ => (hd y).differentiableAt.differentiableWithinAt)
      intro y hy
      rw [(hd y).deriv]
      have hy' : y ∈ Icc 0 m := interior_subset hy
      have hsum := Real.add_rpow_le_rpow_add hy'.1 (sub_nonneg.mpr hy'.2) hq
      rw [add_sub_cancel] at hsum
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hp])
        (by linarith only [hsum])
    have h := hanti ⟨hx, hxm⟩ ⟨hm, le_refl m⟩ hxm
    have hzero : (0 : ℝ) ^ p = 0 := Real.zero_rpow (by linarith : p ≠ 0)
    dsimp only [f] at h
    rw [sub_self, hzero, sub_zero] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hxm), neg_sub]
    have heq : p * m ^ (p - 1) * m = p * m ^ p := by rw [mul_assoc, hpow]
    rw [heq] at h
    linarith only [h]

/-- CO-EXACT-CENTERING: the centered p-th moment of a nonnegative
variable is bounded by the uncentered moment minus the p-th power of its mean. -/
theorem integral_abs_sub_mean_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℝ}
    (hp : 2 ≤ p) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hnonneg : ∀ᵐ omega ∂μ, 0 ≤ X omega) :
    (∫ omega, |X omega - ∫ a, X a ∂μ| ^ p ∂μ) ≤
      (∫ omega, X omega ^ p ∂μ) - (∫ omega, X omega ∂μ) ^ p := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith only [hp])
  have hXi := hX.integrable hp1
  have hm : 0 ≤ ∫ a, X a ∂μ := integral_nonneg_of_ae hnonneg
  have hRawNorm : Integrable (fun omega => ‖X omega‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0] using hX.integrable_norm_rpow'
  have hRaw : Integrable (fun omega => X omega ^ p) μ :=
    hRawNorm.congr (hnonneg.mono fun omega hx => by
      change ‖X omega‖ ^ p = X omega ^ p
      rw [Real.norm_eq_abs, abs_of_nonneg hx])
  have hCentered := hX.sub (memLp_const (∫ a, X a ∂μ))
  have hCenterInt : Integrable (fun omega => |X omega - ∫ a, X a ∂μ| ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs, Pi.sub_apply] using
      hCentered.integrable_norm_rpow'
  have hRight : Integrable (fun omega => X omega ^ p -
      p * (∫ a, X a ∂μ) ^ (p - 1) * X omega +
      (p - 1) * (∫ a, X a ∂μ) ^ p) μ :=
    (hRaw.sub (hXi.const_mul _)).add (integrable_const _)
  have hbound := integral_mono_ae hCenterInt hRight
    (hnonneg.mono fun _ hx => abs_sub_rpow_le_tangent_remainder hx hm hp)
  calc
    _ ≤ ∫ omega, (X omega ^ p - p * (∫ a, X a ∂μ) ^ (p - 1) * X omega +
        (p - 1) * (∫ a, X a ∂μ) ^ p) ∂μ := hbound
    _ = _ := by
      rw [integral_add (f := fun omega => X omega ^ p -
          p * (∫ a, X a ∂μ) ^ (p - 1) * X omega)
          (hRaw.sub (hXi.const_mul _)) (integrable_const _),
        integral_sub hRaw (hXi.const_mul _), integral_const_mul, integral_const,
        probReal_univ, one_smul]
      have hpow : (∫ a, X a ∂μ) ^ (p - 1) * (∫ a, X a ∂μ) =
          (∫ a, X a ∂μ) ^ p := by
        have h := Real.rpow_add_one' (y := p - 1) hm (by linarith : p - 1 + 1 ≠ 0)
        simpa only [sub_add_cancel] using h.symm
      rw [mul_assoc, hpow]
      ring

/-- The uncentered p-th moment alone is therefore also a valid cap. -/
theorem integral_abs_sub_mean_rpow_le_uncentered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℝ}
    (hp : 2 ≤ p) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hnonneg : ∀ᵐ omega ∂μ, 0 ≤ X omega) :
    (∫ omega, |X omega - ∫ a, X a ∂μ| ^ p ∂μ) ≤ ∫ omega, X omega ^ p ∂μ :=
  (integral_abs_sub_mean_rpow_le μ hp hX hnonneg).trans
    (sub_le_self _ (Real.rpow_nonneg (integral_nonneg_of_ae hnonneg) p))

/-- Exact centering has constant one in the real Lp norm, for every real p≥2. -/
theorem lpNorm_sub_mean_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} {p : ℝ}
    (hp : 2 ≤ p) (hX : MemLp X (ENNReal.ofReal p) μ)
    (hnonneg : ∀ᵐ omega ∂μ, 0 ≤ X omega) :
    lpNorm (fun omega => X omega - ∫ a, X a ∂μ) (ENNReal.ofReal p) μ ≤
      lpNorm X (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hCenter : MemLp (fun omega => X omega - ∫ a, X a ∂μ) (ENNReal.ofReal p) μ :=
    hX.sub (memLp_const (∫ a, X a ∂μ))
  rw [lpNorm_eq_integral_norm_rpow_toReal hpne ENNReal.ofReal_ne_top
    hCenter.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal hpne ENNReal.ofReal_ne_top hX.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs]
  apply Real.rpow_le_rpow (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) p)
    _ (inv_nonneg.mpr hp0.le)
  have h := integral_abs_sub_mean_rpow_le_uncentered μ hp hX hnonneg
  have heq : (∫ omega, X omega ^ p ∂μ) = ∫ omega, |X omega| ^ p ∂μ :=
    integral_congr_ae (hnonneg.mono fun omega hx => by
      change X omega ^ p = |X omega| ^ p
      rw [abs_of_nonneg hx])
  rwa [heq] at h

end ASDExplicitGamma.Cold
