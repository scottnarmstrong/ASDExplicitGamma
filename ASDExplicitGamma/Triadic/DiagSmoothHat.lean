module

public import ASDExplicitGamma.Triadic.DiagHat
public import Homogenization.Sobolev.Truncation.Approx
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! Smooth approximations of the DIAG hat and its weak slope. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

/-- One-sided smooth positive parts give smooth hats with bounded slopes. -/
def diagSmoothHat (r ε t : ℝ) : ℝ :=
  (GApprox (-r) ε t - 2 * GApprox 0 ε t + GApprox r ε t) / r

/-- The weak hat slope; its values at the three corners are immaterial. -/
def diagHatSlope (r t : ℝ) : ℝ :=
  ((if -r < t then 1 else 0) - 2 * (if 0 < t then 1 else 0) +
    (if r < t then 1 else 0)) / r

theorem diagHat_eq_positiveParts {r : ℝ} (hr : 0 < r) (t : ℝ) :
    diagHat (t / r) =
      (max (t + r) 0 - 2 * max t 0 + max (t - r) 0) / r := by
  rcases le_total t (-r) with ht | ht
  · rw [max_eq_right (by linarith : t + r ≤ 0),
      max_eq_right (by linarith : t ≤ 0), max_eq_right (by linarith : t - r ≤ 0)]
    rw [diagHat_eq_zero]
    · ring
    · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le)]
      have hdiv : t / r ≤ -1 := (div_le_iff₀ hr).2 (by linarith)
      linarith only [hdiv]
  · rcases le_total t 0 with ht0 | ht0
    · rw [max_eq_left (by linarith : 0 ≤ t + r), max_eq_right ht0,
        max_eq_right (by linarith : t - r ≤ 0)]
      rw [diagHat_left ⟨(le_div_iff₀ hr).2 (by linarith),
        div_nonpos_of_nonpos_of_nonneg ht0 hr.le⟩]
      field_simp
      ring
    · rcases le_total t r with htr | htr
      · rw [max_eq_left (by linarith : 0 ≤ t + r), max_eq_left ht0,
          max_eq_right (sub_nonpos.mpr htr)]
        rw [(diagHat_on_unit ⟨div_nonneg ht0 hr.le, (div_le_one hr).2 htr⟩).1]
        field_simp
        ring
      · rw [max_eq_left (by linarith : 0 ≤ t + r), max_eq_left ht0,
          max_eq_left (sub_nonneg.mpr htr), diagHat_eq_zero]
        · ring
        · rw [abs_of_nonneg (div_nonneg ht0 hr.le)]
          exact (one_le_div hr).2 htr

theorem diagGApprox_contDiff (c ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (GApprox c ε) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (GApprox_hasDerivAt c ε x).differentiableAt, ?_⟩
  rw [deriv_GApprox]
  exact gStep_contDiff c ε

theorem diagSmoothHat_contDiff (r ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (diagSmoothHat r ε) := by
  exact (((diagGApprox_contDiff (-r) ε).sub
    (contDiff_const.mul (diagGApprox_contDiff 0 ε))).add
      (diagGApprox_contDiff r ε)).div_const r

theorem diagSmoothHat_hasDerivAt (r ε t : ℝ) :
    HasDerivAt (diagSmoothHat r ε)
      ((gStep (-r) ε t - 2 * gStep 0 ε t + gStep r ε t) / r) t :=
  (((GApprox_hasDerivAt (-r) ε t).sub
    ((GApprox_hasDerivAt 0 ε t).const_mul 2)).add
      (GApprox_hasDerivAt r ε t)).div_const r

theorem diagSmoothHat_deriv_bound {r : ℝ} (hr : 0 < r) (ε t : ℝ) :
    |deriv (diagSmoothHat r ε) t| ≤ 4 / r := by
  rw [(diagSmoothHat_hasDerivAt r ε t).deriv, abs_div, abs_of_pos hr]
  apply div_le_div_of_nonneg_right _ hr.le
  have h1 := gStep_nonneg (-r) ε t
  have h2 := gStep_le_one (-r) ε t
  have h3 := gStep_nonneg 0 ε t
  have h4 := gStep_le_one 0 ε t
  have h5 := gStep_nonneg r ε t
  have h6 := gStep_le_one r ε t
  exact abs_le.mpr ⟨by linarith only [h1, h3, h4, h5],
    by linarith only [h2, h3, h6]⟩

theorem diagSmoothHat_error {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (t : ℝ) :
    |diagSmoothHat r ε t - diagHat (t / r)| ≤ 8 * ε / r := by
  rw [diagSmoothHat, diagHat_eq_positiveParts hr, ← sub_div, abs_div, abs_of_pos hr]
  apply div_le_div_of_nonneg_right _ hr.le
  have h1 := abs_le.mp (abs_GApprox_sub_le (c := -r) hε t)
  have h2 := abs_le.mp (abs_GApprox_sub_le (c := 0) hε t)
  have h3 := abs_le.mp (abs_GApprox_sub_le (c := r) hε t)
  simp only [sub_neg_eq_add, sub_zero] at h1 h2
  exact abs_le.mpr ⟨by linarith only [h1.1, h2.2, h3.1],
    by linarith only [h1.2, h2.1, h3.2]⟩

theorem diagSmoothHat_tendsto {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => diagSmoothHat r (ε n) t) atTop (𝓝 (diagHat (t / r))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (hlim.const_mul (8 : ℝ)).div_const r
  simp only [mul_zero, zero_div] at h
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => diagSmoothHat_error hr (hε n) t) h

theorem diagSmoothHat_deriv_tendsto {r : ℝ}
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => deriv (diagSmoothHat r (ε n)) t) atTop (𝓝 (diagHatSlope r t)) := by
  simp only [(diagSmoothHat_hasDerivAt r _ t).deriv]
  exact (((tendsto_gStep hε hlim t).sub
    ((tendsto_gStep hε hlim t).const_mul 2)).add
      (tendsto_gStep hε hlim t)).div_const r

end

end ASDExplicitGamma.Triadic
