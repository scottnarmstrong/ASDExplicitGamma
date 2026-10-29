module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import ASDExplicitGamma.Numerics.Native.Heat

/-! Exact scalar Green-kernel mass for the affine positive heat recurrence. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set
open ASDExplicitGamma.Numerics.Native

/-- The affine scalar kernel integrates to the exact exponential difference.
This is the time-`t` Green mass used for the source coefficient
`4 * (exp c - 1)`. -/
theorem nativeHeat_affineGreen_integral (c t : ℝ) (hc : c ≠ 0) :
    (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s))) =
      c⁻¹ * (Real.exp (c * t) - 1) := by
  have hshift :
      (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s))) =
        ∫ s in (0 : ℝ)..t, Real.exp (c * s) := by
    rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => Real.exp (c * x)) t]
    simp
  calc
    _ = ∫ s in (0 : ℝ)..t, Real.exp (c * s) := hshift
    _ = c⁻¹ • ∫ s in (0 : ℝ)..c * t, Real.exp s := by
      rw [intervalIntegral.integral_comp_mul_left (f := fun x : ℝ => Real.exp x) hc]
      simp
    _ = c⁻¹ * (Real.exp (c * t) - 1) := by
      rw [integral_exp, Real.exp_zero, smul_eq_mul]

/-- Pulling the integrating-factor weight outside the integral gives the
standard time-dependent affine Green kernel. -/
theorem nativeHeat_affineGreen_kernelFactor (c t : ℝ) (f : ℝ → ℝ) :
    Real.exp (c * t) * (∫ s in (0 : ℝ)..t, Real.exp (-c * s) * f s) =
      ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * f s := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  change Real.exp (c * t) * (Real.exp (-c * s) * f s) =
    Real.exp (c * (t - s)) * f s
  rw [← mul_assoc, ← Real.exp_add]
  have hexp : c * t + (-c * s) = c * (t - s) := by ring
  rw [hexp]

/-- Integrating the scalar differential inequality with an integrating factor
retains the full time-dependent forcing under the affine Green kernel. -/
theorem nativeHeat_affineGreen_differential (c t : ℝ) (f y yp : ℝ → ℝ)
    (ht : 0 ≤ t)
    (hyDeriv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt y (yp s) s)
    (hIntY : IntervalIntegrable (fun s =>
      Real.exp (-c * s) * yp s - c * Real.exp (-c * s) * y s) volume 0 t)
    (hIntF : IntervalIntegrable (fun s => Real.exp (-c * s) * f s) volume 0 t)
    (hineq : ∀ s ∈ Set.Icc (0 : ℝ) t, yp s ≤ c * y s + f s) :
    y t ≤ Real.exp (c * t) * y 0 +
      ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * f s := by
  let g : ℝ → ℝ := fun s => Real.exp (-c * s) * y s
  have hgDeriv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt g (Real.exp (-c * s) * yp s -
        c * Real.exp (-c * s) * y s) s := by
    intro s hs
    have hExp : HasDerivAt (fun x : ℝ => Real.exp (-c * x))
        (-c * Real.exp (-c * s)) s := by
      have hExp' := (Real.hasDerivAt_exp (-c * s)).comp s
        ((hasDerivAt_id s).const_mul (-c))
      convert hExp' using 1
      · funext x
        congr 1
      · ring
    convert hExp.mul (hyDeriv s hs) using 1
    ring
  have hweighted : ∀ s ∈ Set.Icc (0 : ℝ) t,
      (Real.exp (-c * s) * yp s - c * Real.exp (-c * s) * y s) ≤
        Real.exp (-c * s) * f s := by
    intro s hs
    have hsub : yp s - c * y s ≤ f s := by linarith [hineq s hs]
    calc
      Real.exp (-c * s) * yp s - c * Real.exp (-c * s) * y s =
          Real.exp (-c * s) * (yp s - c * y s) := by ring
      _ ≤ Real.exp (-c * s) * f s :=
        mul_le_mul_of_nonneg_left hsub (Real.exp_nonneg _)
  have hFTC : g t - g 0 ≤ ∫ s in (0 : ℝ)..t, Real.exp (-c * s) * f s := by
    have hEq : g t - g 0 =
        ∫ s in (0 : ℝ)..t,
          (Real.exp (-c * s) * yp s - c * Real.exp (-c * s) * y s) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hgDeriv hIntY]
    rw [hEq]
    exact intervalIntegral.integral_mono_on ht hIntY hIntF hweighted
  have hcancel : Real.exp (c * t) * Real.exp ((-c) * t) = 1 := by
    rw [← Real.exp_add]
    have hx : c * t + (-c) * t = 0 := by ring
    rw [hx, Real.exp_zero]
  have hleft : Real.exp (c * t) * (g t - g 0) =
      y t - Real.exp (c * t) * y 0 := by
    calc
      Real.exp (c * t) * (g t - g 0) =
          Real.exp (c * t) * (Real.exp ((-c) * t) * y t - y 0) := by
            simp [g, Real.exp_zero]
      _ = (Real.exp (c * t) * Real.exp ((-c) * t)) * y t -
          Real.exp (c * t) * y 0 := by ring
      _ = y t - Real.exp (c * t) * y 0 := by rw [hcancel]; ring
  have hmul := mul_le_mul_of_nonneg_left hFTC (Real.exp_nonneg (c * t))
  rw [hleft] at hmul
  calc
    y t = (y t - Real.exp (c * t) * y 0) + Real.exp (c * t) * y 0 := by ring
    _ ≤ (Real.exp (c * t) * (∫ s in (0 : ℝ)..t, Real.exp (-c * s) * f s)) +
        Real.exp (c * t) * y 0 := by linarith
    _ = Real.exp (c * t) * y 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * f s := by
      rw [nativeHeat_affineGreen_kernelFactor]
      ring

/-- A time-dependent lower-degree moment bounded by `A` contributes at most
the same exact Green mass as the constant forcing `4*c*A`. -/
theorem nativeHeat_affineGreen_forcing_le_of_bound (c t A : ℝ) (m : ℝ → ℝ)
    (hc : 0 < c) (ht : 0 ≤ t)
    (hIntM : IntervalIntegrable
      (fun s => Real.exp (c * (t - s)) * (4 * c * m s)) volume 0 t)
    (hIntA : IntervalIntegrable
      (fun s => Real.exp (c * (t - s)) * (4 * c * A)) volume 0 t)
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) t, m s ≤ A) :
    (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * (4 * c * m s)) ≤
      4 * (Real.exp (c * t) - 1) * A := by
  have hcoef : 0 ≤ 4 * c := by positivity
  have hpointwise : ∀ s ∈ Set.Icc (0 : ℝ) t,
      Real.exp (c * (t - s)) * (4 * c * m s) ≤
        Real.exp (c * (t - s)) * (4 * c * A) := by
    intro s hs
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hm s hs) hcoef)
      (Real.exp_nonneg _)
  have hmono := intervalIntegral.integral_mono_on ht hIntM hIntA hpointwise
  have hmass := nativeHeat_affineGreen_integral c t (ne_of_gt hc)
  calc
    (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * (4 * c * m s)) ≤
        ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * (4 * c * A) := hmono
    _ = (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s))) * (4 * c * A) := by
      rw [intervalIntegral.integral_mul_const]
    _ = 4 * (Real.exp (c * t) - 1) * A := by
      rw [hmass]
      field_simp [ne_of_gt hc]

/-- The full affine comparison with an additional nonconstant error source.
The lower-degree term is replaced by its capped Green mass, while the other
source remains under the exact positive kernel. -/
theorem nativeHeat_affineGreen_differential_of_lowerBound_addError
    (c t A : ℝ) (m r y yp : ℝ → ℝ)
    (hc : 0 < c) (ht : 0 ≤ t)
    (hyDeriv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt y (yp s) s)
    (hIntY : IntervalIntegrable (fun s =>
      Real.exp (-c * s) * yp s - c * Real.exp (-c * s) * y s) volume 0 t)
    (hIntSource : IntervalIntegrable
      (fun s => Real.exp (-c * s) * (4 * c * m s + r s)) volume 0 t)
    (hIntGreenM : IntervalIntegrable
      (fun s => Real.exp (c * (t - s)) * (4 * c * m s)) volume 0 t)
    (hIntGreenR : IntervalIntegrable
      (fun s => Real.exp (c * (t - s)) * r s) volume 0 t)
    (hIntGreenA : IntervalIntegrable
      (fun s => Real.exp (c * (t - s)) * (4 * c * A)) volume 0 t)
    (hineq : ∀ s ∈ Set.Icc (0 : ℝ) t,
      yp s ≤ c * y s + 4 * c * m s + r s)
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) t, m s ≤ A) :
    y t ≤ Real.exp (c * t) * y 0 +
      (4 * (Real.exp (c * t) - 1) * A +
        ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * r s) := by
  have hineq' (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) t) :
      yp s ≤ c * y s + (4 * c * m s + r s) := by
    calc
      yp s ≤ c * y s + 4 * c * m s + r s := hineq s hs
      _ = c * y s + (4 * c * m s + r s) := by ring
  have hgreen := nativeHeat_affineGreen_differential c t
    (fun s => 4 * c * m s + r s) y yp ht hyDeriv hIntY hIntSource hineq'
  have hforce := nativeHeat_affineGreen_forcing_le_of_bound c t A m hc ht
    hIntGreenM hIntGreenA hm
  have hsplit :
      (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * (4 * c * m s + r s)) =
        (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * (4 * c * m s)) +
          ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * r s := by
    calc
      _ = ∫ s in (0 : ℝ)..t,
          (Real.exp (c * (t - s)) * (4 * c * m s) +
            Real.exp (c * (t - s)) * r s) := by
              congr 1
              funext s
              ring
      _ = _ := intervalIntegral.integral_add hIntGreenM hIntGreenR
  calc
    y t ≤ Real.exp (c * t) * y 0 +
        ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) *
          (4 * c * m s + r s) := hgreen
    _ = Real.exp (c * t) * y 0 +
        ((∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * (4 * c * m s)) +
          ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * r s) := by rw [hsplit]
    _ ≤ Real.exp (c * t) * y 0 +
        (4 * (Real.exp (c * t) - 1) * A +
          ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * r s) :=
      add_le_add le_rfl (add_le_add hforce le_rfl)

/-- The producer's native scalar coefficient is positive whenever its old-row
scale is positive. -/
theorem nativeHeatExpArg_pos (old : NativeOldRow) (he : 0 < old.e) :
    0 < nativeHeatExpArg old := by
  have hK : 0 < nativeHeatK := by norm_num [nativeHeatK]
  have hM : 0 < nativeHeatM := by norm_num [nativeHeatM]
  have hB : 0 < nativeHeatB := by
    norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
  unfold nativeHeatExpArg
  exact mul_pos he (add_pos (by positivity) (by positivity))

/-- The full positive Green comparison with the exact native old-row drift
and an arbitrary time-dependent VHEAT remainder. The lower-degree moment is
capped separately; the remainder remains under its exact exponential kernel. -/
theorem nativeHeat_affineGreen_nativeOld_differential_of_lowerBound_addError
    (old : NativeOldRow) (he : 0 < old.e) (t A : ℝ)
    (m r y yp : ℝ → ℝ) (ht : 0 ≤ t)
    (hyDeriv : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt y (yp s) s)
    (hIntY : IntervalIntegrable (fun s =>
      Real.exp (-(nativeHeatExpArg old : ℝ) * s) * yp s -
        (nativeHeatExpArg old : ℝ) *
          Real.exp (-(nativeHeatExpArg old : ℝ) * s) * y s) volume 0 t)
    (hIntSource : IntervalIntegrable (fun s =>
      Real.exp (-(nativeHeatExpArg old : ℝ) * s) *
        (4 * (nativeHeatExpArg old : ℝ) * m s + r s)) volume 0 t)
    (hIntGreenM : IntervalIntegrable (fun s =>
      Real.exp ((nativeHeatExpArg old : ℝ) * (t - s)) *
        (4 * (nativeHeatExpArg old : ℝ) * m s)) volume 0 t)
    (hIntGreenR : IntervalIntegrable (fun s =>
      Real.exp ((nativeHeatExpArg old : ℝ) * (t - s)) * r s) volume 0 t)
    (hIntGreenA : IntervalIntegrable (fun s =>
      Real.exp ((nativeHeatExpArg old : ℝ) * (t - s)) *
        (4 * (nativeHeatExpArg old : ℝ) * A) ) volume 0 t)
    (hineq : ∀ s ∈ Set.Icc (0 : ℝ) t,
      yp s ≤ (nativeHeatExpArg old : ℝ) * y s +
        4 * (nativeHeatExpArg old : ℝ) * m s + r s)
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) t, m s ≤ A) :
    y t ≤ Real.exp ((nativeHeatExpArg old : ℝ) * t) * y 0 +
      (4 * (Real.exp ((nativeHeatExpArg old : ℝ) * t) - 1) * A +
        ∫ s in (0 : ℝ)..t,
          Real.exp ((nativeHeatExpArg old : ℝ) * (t - s)) * r s) := by
  have hc : 0 < (nativeHeatExpArg old : ℝ) := by
    exact_mod_cast nativeHeatExpArg_pos old he
  exact nativeHeat_affineGreen_differential_of_lowerBound_addError
    (nativeHeatExpArg old : ℝ) t A m r y yp hc ht hyDeriv hIntY
    hIntSource hIntGreenM hIntGreenR hIntGreenA hineq hm

/-- Time one of the native affine Green comparison has exactly the
producer's coefficients `exp(c)` and `4 * (exp(c) - 1)`, while retaining the
time-dependent VHEAT source under its positive Green kernel. -/
theorem nativeHeat_affineGreen_nativeOld_timeOne_of_lowerBound_addError
    (old : NativeOldRow) (he : 0 < old.e) (A : ℝ)
    (m r y yp : ℝ → ℝ)
    (hyDeriv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt y (yp s) s)
    (hIntY : IntervalIntegrable (fun s =>
      Real.exp (-(nativeHeatExpArg old : ℝ) * s) * yp s -
        (nativeHeatExpArg old : ℝ) *
          Real.exp (-(nativeHeatExpArg old : ℝ) * s) * y s) volume 0 1)
    (hIntSource : IntervalIntegrable (fun s =>
      Real.exp (-(nativeHeatExpArg old : ℝ) * s) *
        (4 * (nativeHeatExpArg old : ℝ) * m s + r s)) volume 0 1)
    (hIntGreenM : IntervalIntegrable (fun s =>
      Real.exp ((nativeHeatExpArg old : ℝ) * (1 - s)) *
        (4 * (nativeHeatExpArg old : ℝ) * m s)) volume 0 1)
    (hIntGreenR : IntervalIntegrable (fun s =>
      Real.exp ((nativeHeatExpArg old : ℝ) * (1 - s)) * r s) volume 0 1)
    (hIntGreenA : IntervalIntegrable (fun s =>
      Real.exp ((nativeHeatExpArg old : ℝ) * (1 - s)) *
        (4 * (nativeHeatExpArg old : ℝ) * A) ) volume 0 1)
    (hineq : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      yp s ≤ (nativeHeatExpArg old : ℝ) * y s +
        4 * (nativeHeatExpArg old : ℝ) * m s + r s)
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) 1, m s ≤ A) :
    y 1 ≤ Real.exp (nativeHeatExpArg old : ℝ) * y 0 +
      (4 * (Real.exp (nativeHeatExpArg old : ℝ) - 1) * A +
        ∫ s in (0 : ℝ)..1,
          Real.exp ((nativeHeatExpArg old : ℝ) * (1 - s)) * r s) := by
  simpa using nativeHeat_affineGreen_nativeOld_differential_of_lowerBound_addError
    old he (1 : ℝ) A m r y yp (by norm_num) hyDeriv hIntY hIntSource
    hIntGreenM hIntGreenR hIntGreenA hineq hm

end ASDExplicitGamma.Native
