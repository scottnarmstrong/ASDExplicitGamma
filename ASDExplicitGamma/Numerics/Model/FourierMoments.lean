module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact monomial Fourier moment recurrences used by the q3 mode certificates. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
open MeasureTheory

noncomputable def cosineMoment (w : ℝ) (n : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, u^n*Real.cos (w*u)
noncomputable def sineMoment (w : ℝ) (n : ℕ) : ℝ :=
  ∫ u in (0 : ℝ)..1, u^n*Real.sin (w*u)

theorem sine_primitive (w x : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.sin (w*u)/w) (Real.cos (w*x)) x := by
  simpa [hw] using ((Real.hasDerivAt_sin (w*x)).comp x
    ((hasDerivAt_id x).const_mul w)).div_const w

theorem cosine_primitive (w x : ℝ) (hw : w ≠ 0) :
    HasDerivAt (fun u : ℝ => -Real.cos (w*u)/w) (Real.sin (w*x)) x := by
  simpa [hw] using (((Real.hasDerivAt_cos (w*x)).comp x
    ((hasDerivAt_id x).const_mul w)).neg).div_const w

theorem cosine_moment_zero (w : ℝ) (hw : w ≠ 0) :
    cosineMoment w 0 = Real.sin w/w := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => sine_primitive w x hw)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
  simpa [cosineMoment] using h

theorem sine_moment_zero (w : ℝ) (hw : w ≠ 0) :
    sineMoment w 0 = (1-Real.cos w)/w := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => cosine_primitive w x hw)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
  simp only [mul_one, mul_zero, Real.cos_zero] at h
  simp only [sineMoment,pow_zero,one_mul]
  rw [h]
  ring

theorem cosine_moment_succ (w : ℝ) (hw : w ≠ 0) (n : ℕ) :
    cosineMoment w (n+1) = (Real.sin w-(n+1)*sineMoment w n)/w := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => (hasDerivAt_id x).pow (n+1))
    (fun x _ => sine_primitive w x hw)
    (by
      change IntervalIntegrable (fun x : ℝ => ((n+1 : ℕ) : ℝ)*x^n*1) volume 0 1
      exact ((continuous_const.mul (continuous_id.pow n)).mul continuous_const).intervalIntegrable 0 1)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
  have he : (fun x : ℝ => ((n+1 : ℕ) : ℝ)*x^n*(Real.sin (w*x)/w)) =
      (fun x : ℝ => (((n+1 : ℕ) : ℝ)/w)*(x^n*Real.sin (w*x))) := by
    funext x
    ring
  simp only [Nat.add_sub_cancel, id_eq, mul_zero,
    mul_one, Real.sin_zero] at h
  rw [he, intervalIntegral.integral_const_mul] at h
  change cosineMoment w (n+1) = _ at h
  rw [h]
  dsimp [sineMoment]
  push_cast
  ring

theorem sine_moment_succ (w : ℝ) (hw : w ≠ 0) (n : ℕ) :
    sineMoment w (n+1) = (-Real.cos w+(n+1)*cosineMoment w n)/w := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => (hasDerivAt_id x).pow (n+1))
    (fun x _ => cosine_primitive w x hw)
    (by
      change IntervalIntegrable (fun x : ℝ => ((n+1 : ℕ) : ℝ)*x^n*1) volume 0 1
      exact ((continuous_const.mul (continuous_id.pow n)).mul continuous_const).intervalIntegrable 0 1)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
  have he : (fun x : ℝ => ((n+1 : ℕ) : ℝ)*x^n*(-Real.cos (w*x)/w)) =
      (fun x : ℝ => -(((n+1 : ℕ) : ℝ)/w)*(x^n*Real.cos (w*x))) := by
    funext x
    ring
  simp only [Nat.add_sub_cancel, id_eq, mul_zero,
    mul_one, Real.cos_zero] at h
  rw [he, intervalIntegral.integral_const_mul] at h
  change sineMoment w (n+1) = _ at h
  rw [h]
  dsimp [cosineMoment]
  push_cast
  ring

end ASDExplicitGamma.Numerics.Model
