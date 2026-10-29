module

public import ASDExplicitGamma.Triadic.SensitivityDerivativeEstimate

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! One-dimensional integration lemmas for the coarse-sensitivity path. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

noncomputable section

private theorem sensitivity_le_add_of_hasDerivAt_le {y y' : ℝ → ℝ} {B t₁ t₂ : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ)
    (hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → y' τ ≤ B) (ht : t₁ ≤ t₂) :
    y t₂ ≤ y t₁ + B * (t₂ - t₁) := by
  set z : ℝ → ℝ := fun τ => y τ - B * τ with hz
  have hzderiv : ∀ τ, HasDerivAt z (y' τ - B) τ := by
    intro τ
    have hlin : HasDerivAt (fun σ : ℝ => B * σ) B τ := by
      simpa using (hasDerivAt_id τ).const_mul B
    exact (hderiv τ).sub hlin
  have hanti : AntitoneOn z (Set.Icc t₁ t₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₁ t₂) ?_ ?_ ?_
    · exact fun τ _ => ((hzderiv τ).continuousAt).continuousWithinAt
    · exact fun τ _ => (hzderiv τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hmem : τ ∈ Set.Ioo t₁ t₂ := hτ
      rw [(hzderiv τ).deriv]
      linarith [hbound τ hmem.1.le hmem.2.le]
  have hle : z t₂ ≤ z t₁ :=
    hanti (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht
  rw [hz] at hle
  linarith

/-- Variable-coefficient Grönwall for a differentiable scalar path. The
integrating factor is built from the actual interval integral of the
continuous coefficient. -/
theorem sensitivity_exp_integral_of_hasDerivAt_le
    {y y' c : ℝ → ℝ} {t₁ t₂ : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ)
    (hc : Continuous c)
    (hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → y' τ ≤ c τ * y τ)
    (ht : t₁ ≤ t₂) :
    y t₂ ≤ Real.exp (∫ τ in t₁..t₂, c τ) * y t₁ := by
  let I : ℝ → ℝ := fun t => ∫ τ in t₁..t, c τ
  let z : ℝ → ℝ := fun t => Real.exp (-I t) * y t
  have hI : ∀ τ, HasDerivAt I (c τ) τ := by
    intro τ
    exact (hc.integral_hasStrictDerivAt t₁ τ).hasDerivAt
  have hz : ∀ τ, HasDerivAt z
      (Real.exp (-I τ) * (y' τ - c τ * y τ)) τ := by
    intro τ
    have hneg := (hI τ).neg
    have hexp := hneg.exp
    have hmul := hexp.mul (hderiv τ)
    change HasDerivAt (fun t => Real.exp (-I t) * y t)
      (Real.exp (-I τ) * (y' τ - c τ * y τ)) τ
    convert hmul using 1
    simp only [Pi.neg_apply]
    ring
  have hanti : AntitoneOn z (Set.Icc t₁ t₂) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₁ t₂) ?_ ?_ ?_
    · exact fun τ _ => ((hz τ).continuousAt).continuousWithinAt
    · exact fun τ _ => (hz τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hmem : τ ∈ Set.Ioo t₁ t₂ := hτ
      rw [(hz τ).deriv]
      have he := Real.exp_pos (-I τ)
      have hb := hbound τ hmem.1.le hmem.2.le
      nlinarith
  have hle : z t₂ ≤ z t₁ :=
    hanti (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht
  have hIleft : I t₁ = 0 := by simp [I]
  have hIright : I t₂ = ∫ τ in t₁..t₂, c τ := rfl
  have hle' : Real.exp (-(∫ τ in t₁..t₂, c τ)) * y t₂ ≤
      Real.exp (-(0 : ℝ)) * y t₁ := by
    simpa [z, I, hIleft, hIright] using hle
  have he : 0 < Real.exp (∫ τ in t₁..t₂, c τ) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hle' he.le
  calc
    y t₂ = Real.exp (∫ τ in t₁..t₂, c τ) *
        (Real.exp (-(∫ τ in t₁..t₂, c τ)) * y t₂) := by
          rw [← mul_assoc, ← Real.exp_add]
          simp
    _ ≤ Real.exp (∫ τ in t₁..t₂, c τ) * y t₁ := by
          simpa using hmul

/-- The reverse comparison under the corresponding lower differential
inequality. -/
theorem sensitivity_le_exp_integral_mul_of_neg_hasDerivAt_le
    {y y' c : ℝ → ℝ} {t₁ t₂ : ℝ}
    (hderiv : ∀ τ, HasDerivAt y (y' τ) τ)
    (hc : Continuous c)
    (hbound : ∀ τ, t₁ ≤ τ → τ ≤ t₂ → -(c τ * y τ) ≤ y' τ)
    (ht : t₁ ≤ t₂) :
    y t₁ ≤ Real.exp (∫ τ in t₁..t₂, c τ) * y t₂ := by
  let I : ℝ → ℝ := fun t => ∫ τ in t₁..t, c τ
  let z : ℝ → ℝ := fun t => Real.exp (I t) * y t
  have hI : ∀ τ, HasDerivAt I (c τ) τ := by
    intro τ
    exact (hc.integral_hasStrictDerivAt t₁ τ).hasDerivAt
  have hz : ∀ τ, HasDerivAt z
      (Real.exp (I τ) * (y' τ + c τ * y τ)) τ := by
    intro τ
    have hexp := (hI τ).exp
    have hmul := hexp.mul (hderiv τ)
    change HasDerivAt (fun t => Real.exp (I t) * y t)
      (Real.exp (I τ) * (y' τ + c τ * y τ)) τ
    convert hmul using 1
    ring
  have hmono : MonotoneOn z (Set.Icc t₁ t₂) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t₁ t₂) ?_ ?_ ?_
    · exact fun τ _ => ((hz τ).continuousAt).continuousWithinAt
    · exact fun τ _ => (hz τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hmem : τ ∈ Set.Ioo t₁ t₂ := hτ
      rw [(hz τ).deriv]
      have he := Real.exp_pos (I τ)
      have hb := hbound τ hmem.1.le hmem.2.le
      nlinarith
  have hle : z t₁ ≤ z t₂ :=
    hmono (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht
  have hIleft : I t₁ = 0 := by simp [I]
  have hIright : I t₂ = ∫ τ in t₁..t₂, c τ := rfl
  simpa [z, hIleft, hIright] using hle

/-- Bihari's rational envelope from a two-time exponential ratio. -/
theorem sensitivity_bihari_upper_envelope
    {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hC : 0 ≤ C)
    (hf_nonneg : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f t)
    (hRatio : ∀ t, 0 ≤ t → t ≤ 1 →
      f t ≤ Real.exp (∫ τ in (0:ℝ)..t, C * f τ) * f 0)
    (hsmall : C * f 0 < 1) :
    f 1 ≤ f 0 / (1 - C * f 0) := by
  let c : ℝ → ℝ := fun t => C * f t
  let I : ℝ → ℝ := fun t => C * (∫ τ in (0:ℝ)..t, f τ)
  let W : ℝ → ℝ := fun t => Real.exp (-I t)
  have hIf : ∀ t, HasDerivAt (fun s => ∫ τ in (0:ℝ)..s, f τ) (f t) t := by
    intro t
    exact (hf.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hI : ∀ t, HasDerivAt I (c t) t := by
    intro t
    have h := (hIf t).const_mul C
    simpa [I, c] using h
  have hW : ∀ t, HasDerivAt W (-(C * f t) * W t) t := by
    intro t
    have hlin := (hI t).const_mul (-1)
    have hexp := hlin.exp
    change HasDerivAt (fun s => Real.exp (-I s))
      (-(C * f t) * W t) t
    convert hexp using 1
    · funext s
      congr 1
      ring
    · simp only [W, c]
      ring_nf
  have hLW (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      f t * W t ≤ f 0 := by
    have hr := hRatio t ht0 ht1
    have hw : 0 < W t := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hr hw.le
    have hexp : Real.exp (I t) * Real.exp (-I t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      f t * W t = f t * Real.exp (-I t) := rfl
      _ ≤ (Real.exp (I t) * f 0) * Real.exp (-I t) := by
        simpa [I, W] using hmul
      _ = f 0 := by rw [show (Real.exp (I t) * f 0) * Real.exp (-I t) =
          f 0 * (Real.exp (I t) * Real.exp (-I t)) by ring, hexp, mul_one]
  have hgderiv : ∀ t, HasDerivAt (-W)
      (C * f t * W t) t := by
    intro t
    have h := (hW t).neg
    convert h using 1
    · ring
  have hgbound : ∀ t, 0 ≤ t → t ≤ 1 → C * f t * W t ≤ C * f 0 := by
    intro t ht0 ht1
    have hprod := mul_le_mul_of_nonneg_left (hLW t ht0 ht1) hC
    nlinarith [hprod]
  have hstep := sensitivity_le_add_of_hasDerivAt_le hgderiv hgbound
    (by norm_num : (0 : ℝ) ≤ 1)
  have hI0 : I 0 = 0 := by simp [I]
  have hW0 : W 0 = 1 := by simp [W, hI0]
  simp only [sub_zero, mul_one] at hstep
  change -W 1 ≤ -W 0 + C * f 0 at hstep
  simp only [hW0] at hstep
  have hW1 : 1 - C * f 0 ≤ W 1 := by
    linarith
  have hden : 0 < 1 - C * f 0 := by linarith
  have hfinalProd : f 1 * (1 - C * f 0) ≤ f 0 := by
    calc
      f 1 * (1 - C * f 0) ≤ f 1 * W 1 :=
        mul_le_mul_of_nonneg_left hW1 (hf_nonneg 1 (by norm_num) (by norm_num))
      _ ≤ f 0 := hLW 1 (by norm_num) (by norm_num)
  exact (le_div_iff₀ hden).2 hfinalProd

/-- Pointwise Bihari envelope. Under the same two-time ratio as above, the
rational bound holds at every intermediate path time. -/
theorem sensitivity_bihari_upper_envelope_at
    {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hC : 0 ≤ C)
    (hf_nonneg : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f t)
    (hRatio : ∀ t, 0 ≤ t → t ≤ 1 →
      f t ≤ Real.exp (∫ τ in (0:ℝ)..t, C * f τ) * f 0)
    (hsmall : C * f 0 < 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f t ≤ f 0 / (1 - C * f 0 * t) := by
  let c : ℝ → ℝ := fun s => C * f s
  let I : ℝ → ℝ := fun s => C * (∫ τ in (0:ℝ)..s, f τ)
  let W : ℝ → ℝ := fun s => Real.exp (-I s)
  have hIf : ∀ s, HasDerivAt (fun r => ∫ τ in (0:ℝ)..r, f τ) (f s) s := by
    intro s
    exact (hf.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hI : ∀ s, HasDerivAt I (c s) s := by
    intro s
    have h := (hIf s).const_mul C
    simpa [I, c] using h
  have hW : ∀ s, HasDerivAt W (-(C * f s) * W s) s := by
    intro s
    have hlin := (hI s).const_mul (-1)
    have hexp := hlin.exp
    change HasDerivAt (fun r => Real.exp (-I r))
      (-(C * f s) * W s) s
    convert hexp using 1
    · funext r
      congr 1
      ring
    · simp only [W, c]
      ring_nf
  have hLW : f t * W t ≤ f 0 := by
    have hr := hRatio t ht0 ht1
    have hw : 0 < W t := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hr hw.le
    have hexp : Real.exp (I t) * Real.exp (-I t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    calc
      f t * W t = f t * Real.exp (-I t) := rfl
      _ ≤ (Real.exp (I t) * f 0) * Real.exp (-I t) := by
        simpa [I, W] using hmul
      _ = f 0 := by
        rw [show (Real.exp (I t) * f 0) * Real.exp (-I t) =
          f 0 * (Real.exp (I t) * Real.exp (-I t)) by ring, hexp, mul_one]
  have hgderiv : ∀ s, HasDerivAt (-W)
      (C * f s * W s) s := by
    intro s
    have h := (hW s).neg
    convert h using 1
    · ring
  have hgBound : ∀ s, 0 ≤ s → s ≤ t → C * f s * W s ≤ C * f 0 := by
    intro s hs0 hst
    have hs1 : s ≤ 1 := hst.trans ht1
    have hprod := mul_le_mul_of_nonneg_left (show f s * W s ≤ f 0 from by
      have hr := hRatio s hs0 hs1
      have hw : 0 < W s := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hr hw.le
      have hexp : Real.exp (I s) * Real.exp (-I s) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc
        f s * W s = f s * Real.exp (-I s) := rfl
        _ ≤ (Real.exp (I s) * f 0) * Real.exp (-I s) := by
          simpa [I, W] using hmul
        _ = f 0 := by
          rw [show (Real.exp (I s) * f 0) * Real.exp (-I s) =
            f 0 * (Real.exp (I s) * Real.exp (-I s)) by ring, hexp, mul_one]) hC
    nlinarith [hprod]
  have hstep := sensitivity_le_add_of_hasDerivAt_le hgderiv hgBound (by linarith)
  have hI0 : I 0 = 0 := by simp [I]
  have hW0 : W 0 = 1 := by simp [W, hI0]
  have hWlower : 1 - C * f 0 * t ≤ W t := by
    have hstep' : -(W t) ≤ -1 + C * f 0 * t := by
      simpa only [Pi.neg_apply, hW0, sub_zero] using hstep
    linarith
  have hf0 : 0 ≤ f 0 := hf_nonneg 0 (by norm_num) (by norm_num)
  have hden : 0 < 1 - C * f 0 * t := by
    have hprod : 0 ≤ C * f 0 := mul_nonneg hC hf0
    nlinarith
  have hfinal : f t * (1 - C * f 0 * t) ≤ f 0 := by
    calc
      f t * (1 - C * f 0 * t) ≤ f t * W t :=
        mul_le_mul_of_nonneg_left hWlower (hf_nonneg t ht0 ht1)
      _ ≤ f 0 := hLW
  exact (le_div_iff₀ hden).2 hfinal

end

end ASDExplicitGamma.Triadic
