module

public import ASDExplicitGamma.Gaussian.RioScalar
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Quadratic Taylor comparison and regularization for the sharp Lp norm -/

@[expose] public section

open Set

namespace ASDExplicitGamma.Gaussian

/-- A global upper second-derivative bound and vanishing initial slope give the exact
one-half Taylor constant. -/
theorem rio_taylor_quadratic_le {f df ddf : ℝ → ℝ} {C : ℝ}
    (hd : ∀ t, HasDerivAt f (df t) t) (hdd : ∀ t, HasDerivAt df (ddf t) t)
    (hbound : ∀ t, ddf t ≤ C) (hzero : df 0 = 0) : f 1 ≤ f 0 + C / 2 := by
  have hlin (t : ℝ) (ht : 0 ≤ t) : df t ≤ C * t := by
    have hh := image_sub_le_mul_sub_of_deriv_le (fun t => (hdd t).differentiableAt)
      (fun t => by rw [(hdd t).deriv]; exact hbound t) ht
    simpa only [hzero, sub_zero] using hh
  let F : ℝ → ℝ := fun t => f t - C / 2 * t ^ 2
  have hF (t : ℝ) : HasDerivAt F (df t - C * t) t := by
    convert (hd t).sub (((hasDerivAt_id' t).pow 2).const_mul (C / 2)) using 1
    ring
  have hanti : AntitoneOn F (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact sub_nonpos.mpr (hlin t (interior_subset ht))
  have hh := hanti (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show (1 : ℝ) ∈ Ici 0 by norm_num) (by norm_num)
  dsimp only [F] at hh
  norm_num only [zero_pow (by norm_num : 2 ≠ 0), one_pow, mul_zero, sub_zero] at hh
  linarith only [hh]

/-- Adding ε to the moment handles zero norms without assuming any nondegeneracy. -/
theorem rio_regularized_second_bound {r a b c K ε : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 ≤ a) (hK : 0 ≤ K) (hε : 0 < ε)
    (hc : c ≤ r⁻¹ * a ^ (1 - r) * K) :
    r * (r - 1) * (a + ε) ^ (r - 2) * b ^ 2 +
      r * (a + ε) ^ (r - 1) * c ≤ K := by
  have hae : 0 < a + ε := add_pos_of_nonneg_of_pos ha hε
  have hprod : (a + ε) ^ (r - 1) * a ^ (1 - r) ≤ 1 := by
    calc
      _ ≤ (a + ε) ^ (r - 1) * (a + ε) ^ (1 - r) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha (by linarith only [hε]) (sub_nonneg.mpr hr1))
          (Real.rpow_nonneg hae.le _)
      _ = 1 := by rw [← Real.rpow_add hae]; simp only [sub_add_sub_cancel, sub_self, Real.rpow_zero]
  have hneg : r * (r - 1) * (a + ε) ^ (r - 2) * b ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr.le (sub_nonpos.mpr hr1))
        (Real.rpow_nonneg hae.le _)) (sq_nonneg b)
  have hscale : 0 ≤ r * (a + ε) ^ (r - 1) := mul_nonneg hr.le (Real.rpow_nonneg hae.le _)
  have he : r * (a + ε) ^ (r - 1) * (r⁻¹ * a ^ (1 - r) * K) =
      ((a + ε) ^ (r - 1) * a ^ (1 - r)) * K := by
    calc
      _ = (r * r⁻¹) * ((a + ε) ^ (r - 1) * a ^ (1 - r)) * K := by ring
      _ = _ := by rw [mul_inv_cancel₀ hr.ne', one_mul]
  have hh := mul_le_mul_of_nonneg_left hc hscale
  rw [he] at hh
  have hfinal := hh.trans (mul_le_mul_of_nonneg_right hprod hK)
  rw [one_mul] at hfinal
  exact (add_le_add hneg hfinal).trans_eq (zero_add K)

end ASDExplicitGamma.Gaussian
