module

public import ASDExplicitGamma.Native.OldSignedMaxHistoryAffine

/-! The auxiliary affine history fits inside the unchanged OLD panel envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Elementary comparison with the source square-root history profile.
These are scalar endpoint gates, not assumptions on a random source quantity. -/
theorem old_signed_affine_le_history_profile (H0 Δ v C t : ℝ)
    (hH0 : 2279/1000≤H0) (hΔ : 17/125≤Δ) (hv : 153/100000≤v)
    (hC : 31/20≤C) (ht0 : 0≤t) (ht1 : t≤1) :
    (217/100:ℝ)+(49/100)*t ≤ (Real.sqrt (H0+Δ*t)+Real.sqrt (2*v*t)*C)^2 := by
  have hH : 0≤H0 := (by norm_num : (0:ℝ)≤2279/1000).trans hH0
  have hD : 0≤Δ := (by norm_num : (0:ℝ)≤17/125).trans hΔ
  have hv0 : 0≤v := (by norm_num : (0:ℝ)≤153/100000).trans hv
  have hC0 : 0≤C := (by norm_num : (0:ℝ)≤31/20).trans hC
  have ht2 : t^2≤t := by nlinarith only [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have ha : (3/2:ℝ)≤Real.sqrt (H0+Δ*t) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith only [hH0,mul_nonneg hD ht0]
  have hb : (11/200:ℝ)*t≤Real.sqrt (2*v*t) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    have hvt := mul_le_mul_of_nonneg_right hv ht0
    nlinarith only [hvt,ht2,ht0]
  have hbc : (341/4000:ℝ)*t≤Real.sqrt (2*v*t)*C := by
    have hh := mul_le_mul hb hC (by norm_num : (0:ℝ)≤31/20) (Real.sqrt_nonneg _)
    nlinarith only [hh]
  have hcross := mul_le_mul ha hbc (by positivity : (0:ℝ)≤(341/4000)*t) (Real.sqrt_nonneg _)
  have hasq := Real.sq_sqrt (add_nonneg hH (mul_nonneg hD ht0))
  have hdt := mul_le_mul_of_nonneg_right hΔ ht0
  nlinarith only [hH0,hdt,ht1,hcross,hasq,sq_nonneg (Real.sqrt (2*v*t)*C)]

/-- The literal inverse-bank and rare-root multiplier passes the scalar
history comparison gate, without suppressing its positive rare term. -/
theorem old_signed_panel_history_multiplier :
    (31/20:ℝ)≤(3:ℝ)^(1/4:ℝ)*Real.sqrt (3683/2500:ℝ)+
      (105:ℝ)^(1/8:ℝ)*Real.sqrt (3/10^46:ℝ) := by
  have h3 : (13/10:ℝ)≤(3:ℝ)^(1/4:ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num) (by positivity)
      (by norm_num : (4:ℕ)≠0)).mp
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    norm_num
  have hb : (6/5:ℝ)≤Real.sqrt (3683/2500:ℝ) :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hh := mul_le_mul h3 hb (by norm_num : (0:ℝ)≤6/5) (by positivity)
  have hr : 0≤(105:ℝ)^(1/8:ℝ)*Real.sqrt (3/10^46:ℝ) := by positivity
  linarith only [hh,hr]

end
end ASDExplicitGamma.Native
