module

public import ASDExplicitGamma.Gaussian.RioTaylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Regularized integration of the sharp squared-norm second variation -/

@[expose] public section

open Set Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The analytic comparison behind one-step Lp smoothness. The source moment supplies
all derivative and Hölder premises internally in `rio_lp_smoothness`. -/
theorem rio_norm_square_le_of_moment {f df ddf : ℝ → ℝ} {p L : ℝ}
    (hp : 2 ≤ p) (hf : ∀ t, 0 ≤ f t) (hL : 0 ≤ L)
    (hd : ∀ t, HasDerivAt f (df t) t) (hdd : ∀ t, HasDerivAt df (ddf t) t)
    (hbound : ∀ t, ddf t ≤ p * (p - 1) * f t ^ ((p - 2) / p) * L)
    (hzero : df 0 = 0) : f 1 ^ (2 / p) ≤ f 0 ^ (2 / p) + (p - 1) * L := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  let r := 2 / p
  let K := 2 * (p - 1) * L
  have hr : 0 < r := div_pos (by norm_num) hp0
  have hr1 : r ≤ 1 := (div_le_one hp0).mpr hp
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hp])) hL
  have hri : r⁻¹ = p / 2 := by dsimp only [r]; field_simp
  have hrex : (p - 2) / p = 1 - r := by dsimp only [r]; field_simp
  have he (ε : ℝ) (hε : 0 < ε) : (f 1 + ε) ^ r ≤ (f 0 + ε) ^ r + (p - 1) * L := by
    let g : ℝ → ℝ := fun t => (f t + ε) ^ r
    let dg : ℝ → ℝ := fun t => r * (f t + ε) ^ (r - 1) * df t
    let ddg : ℝ → ℝ := fun t => r * (r - 1) * (f t + ε) ^ (r - 2) * df t ^ 2 +
      r * (f t + ε) ^ (r - 1) * ddf t
    have hpos (t : ℝ) : 0 < f t + ε := add_pos_of_nonneg_of_pos (hf t) hε
    have hg (t : ℝ) : HasDerivAt g (dg t) t := by
      convert ((hd t).add_const ε).rpow_const (p := r) (Or.inl (hpos t).ne') using 1
      ring
    have hdg (t : ℝ) : HasDerivAt dg (ddg t) t := by
      convert ((((hd t).add_const ε).rpow_const (p := r - 1) (Or.inl (hpos t).ne')).const_mul r).mul (hdd t) using 1
      dsimp only [ddg]
      have heq : r - 1 - 1 = r - 2 := by ring
      rw [heq]
      ring
    have hddg (t : ℝ) : ddg t ≤ K := by
      apply rio_regularized_second_bound hr hr1 (hf t) hK hε
      have hb := hbound t
      rw [hrex] at hb
      convert hb using 1
      rw [hri]
      dsimp only [K]
      ring
    have h0 : dg 0 = 0 := by dsimp only [dg]; rw [hzero, mul_zero]
    have ht := rio_taylor_quadratic_le hg hdg hddg h0
    change (f 1 + ε) ^ r ≤ (f 0 + ε) ^ r + K / 2 at ht
    convert ht using 1
    dsimp only [K]
    ring
  have hc (t : ℝ) : ContinuousAt (fun ε : ℝ => (f t + ε) ^ r) 0 :=
    (continuousAt_const.add continuousAt_id).rpow_const (Or.inr hr.le)
  have hlim := (hc 1).tendsto.sub (hc 0).tendsto
  simp only [add_zero] at hlim
  have hh : f 1 ^ r - f 0 ^ r ≤ (p - 1) * L := by
    apply le_of_tendsto (hlim.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin] with ε hε
    linarith only [he ε hε]
  change f 1 ^ r ≤ f 0 ^ r + (p - 1) * L
  linarith only [hh]

end ASDExplicitGamma.Gaussian
