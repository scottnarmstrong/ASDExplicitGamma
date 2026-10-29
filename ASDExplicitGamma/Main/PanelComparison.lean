module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp

/-! The affine comparison on an absolutely continuous panel, MA-PANEL-COMPARISON. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory

/-- The exact affine panel update. -/
noncomputable def panelMap (A ell dt u : ℝ) : ℝ :=
  Real.exp (-ell * dt) * u + A * (1 - Real.exp (-ell * dt)) / ell

/-- Increasing dependence on the entering value. -/
theorem panelMap_mono (A ell dt : ℝ) : Monotone (panelMap A ell dt) := by
  intro u v huv
  exact add_le_add (mul_le_mul_of_nonneg_left huv (Real.exp_pos _).le) le_rfl

/-- Fundamental theorem comparison for an absolutely continuous function
with nonpositive derivative almost everywhere on its panel. -/
theorem panel_endpoint_le_of_deriv_nonpos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ Icc a b → deriv f t ≤ 0) : f b ≤ f a := by
  have hint := intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
    ((ae_restrict_iff' measurableSet_Icc).mpr hd)
  rw [hf.integral_deriv_eq_sub, intervalIntegral.integral_zero] at hint
  linarith only [hint]

/-- Integrating factor argument for the source a.e. affine differential inequality.
The bound holds without sign restrictions on `f` and `A`. -/
theorem panel_comparison {f : ℝ → ℝ} {a b A ell : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) (hell : 0 < ell)
    (hd : ∀ᵐ t, t ∈ Icc a b → deriv f t ≤ A - ell * f t) :
    f b ≤ panelMap A ell (b - a) (f a) := by
  let g : ℝ → ℝ := fun t => Real.exp (ell * (t - a)) * (f t - A / ell)
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (ell * (t - a))) :=
    Real.contDiff_exp.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  have hg : AbsolutelyContinuousOnInterval g a b :=
    he.contDiffOn.absolutelyContinuousOnInterval.fun_mul (hf.sub ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => A / ell)).contDiffOn.absolutelyContinuousOnInterval))
  have hgd : ∀ᵐ t, t ∈ Icc a b → deriv g t ≤ 0 := by
    filter_upwards [hf.ae_differentiableAt, hd] with t hft hdt ht
    have hft' := (hft (by rwa [uIcc_of_le hab])).hasDerivAt
    have he' := ((hasDerivAt_id t).sub_const a).const_mul ell |>.exp
    have hder := he'.mul (hft'.sub_const (A / ell))
    change HasDerivAt g _ t at hder
    rw [hder.deriv]
    have hsign : ell * (f t - A / ell) + deriv f t ≤ 0 := by
      rw [mul_sub, mul_div_cancel₀ _ hell.ne']
      linarith only [hdt ht]
    calc
      _ = Real.exp (ell * (t - a)) * (ell * (f t - A / ell) + deriv f t) := by
        simp only [id_eq, mul_one]
        ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hsign
  have hbound := panel_endpoint_le_of_deriv_nonpos hab hg hgd
  have hdiv : f b - A / ell ≤ Real.exp (-(ell * (b - a))) * (f a - A / ell) := by
    rw [Real.exp_neg, mul_comm _ (f a - A / ell), ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos (ell * (b - a)))).mpr
    dsimp [g] at hbound
    simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at hbound
    simpa only [mul_comm] using hbound
  dsimp [panelMap]
  rw [neg_mul]
  have halg : Real.exp (-(ell * (b - a))) * f a +
      A * (1 - Real.exp (-(ell * (b - a)))) / ell =
      Real.exp (-(ell * (b - a))) * (f a - A / ell) + A / ell := by ring
  rw [halg]
  linarith only [hdiv]

/-- The same affine comparison at every time in the panel. -/
theorem panel_comparison_on {f : ℝ → ℝ} {a b A ell : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b) (hell : 0 < ell)
    (hd : ∀ᵐ t, t ∈ Icc a b → deriv f t ≤ A - ell * f t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    f t ≤ panelMap A ell (t - a) (f a) := by
  apply panel_comparison ht.1 (hf.mono (by
    rw [uIcc_of_le hab, uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2)) hell
  filter_upwards [hd] with s hs hs'
  exact hs ⟨hs'.1, hs'.2.trans ht.2⟩

end ASDExplicitGamma.Main
