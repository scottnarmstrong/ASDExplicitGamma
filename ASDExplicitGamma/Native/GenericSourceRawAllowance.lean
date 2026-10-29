module

public import ASDExplicitGamma.Native.GenericSourceBandProfile

/-! The outward raw source profile is covered by the stronger native clock,
without altering its initial allowance or any complete-tail allocation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Algsuperdiff.Section3
open ASDExplicitGamma.Inverse
noncomputable section

/-- At every source depth h≥9 the raw clock pays at least 1.5 theta, using
only its positive linear height term. -/
theorem native_source_raw_increment_lower (M : ABKModel 2) (height : ℕ) (hh : 9 ≤ height) :
    (3/2:ℝ)*theta M ≤ nativeSourceRawMomentIncrement height
      (nativeSourceRawShellVarianceCap M.gamma height) (nativeSourceFullResponseCap M.gamma height) := by
  let e := nativeSourceRawShellVarianceCap M.gamma height
  let f := nativeSourceFullResponseCap M.gamma height
  let H := nativeSourceRawMomentIncrement height e f
  have hg := M.shellPrefix.gamma_pos.le
  have hf : 0 ≤ f := by dsimp [f,nativeSourceFullResponseCap,rawTraceFullResponseCap]; positivity
  have he : 0 ≤ e := by dsimp [e,nativeSourceRawShellVarianceCap]; positivity
  have hp : 1 ≤ (3:ℝ)^(2*(height:ℝ)*M.gamma) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have he_lower : (9/2:ℝ)*M.gamma ≤ e := by
    dsimp only [e,nativeSourceRawShellVarianceCap]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤(9/2)*M.gamma by positivity)
  have hheight : (9:ℝ) ≤ height := by exact_mod_cast hh
  have hbaseline : (78*(9:ℝ)*nativeSourceB128)*e ≤ H := by
    dsimp [H,nativeSourceRawMomentIncrement]
    have h1 := mul_le_mul_of_nonneg_right hheight (show (0:ℝ)≤78*nativeSourceB128 by norm_num [nativeSourceB128])
    have hrest : 0 ≤ 76*nativeSourceK*nativeSourceB128+
      2*nativeSourceK*nativeSourceB128*f+(nativeSourceM+38*nativeSourceQ)*nativeSourceB128^2*f := by
      dsimp [nativeSourceK,nativeSourceM,nativeSourceQ,nativeSourceB128]
      positivity
    nlinarith only [mul_nonneg he hrest,mul_le_mul_of_nonneg_right h1 he]
  have hscale := mul_le_mul_of_nonneg_left he_lower
    (show (0:ℝ)≤78*(9:ℝ)*nativeSourceB128 by norm_num [nativeSourceB128])
  dsimp [nativeSourceB128] at hbaseline hscale
  dsimp [theta,gammaZero]
  change _ ≤ H
  linarith only [hbaseline,hscale,hg]

/-- The saved fifth of the raw increment covers the difference between the
native singleton start and the exact source-program raw initial allowance. -/
theorem native_source_raw_initial_allowance (M : ABKModel 2) (height : ℕ) (hh : 9 ≤ height) :
    (2013/10000:ℝ)*theta M+(4/5:ℝ)*nativeSourceRawMomentIncrement height
      (nativeSourceRawShellVarianceCap M.gamma height) (nativeSourceFullResponseCap M.gamma height) ≤
      nativeSourceAverageFactor*((3/50:ℝ)*theta M)+nativeSourceRawMomentIncrement height
        (nativeSourceRawShellVarianceCap M.gamma height) (nativeSourceFullResponseCap M.gamma height) := by
  have hH := native_source_raw_increment_lower M height hh
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  norm_num [nativeSourceAverageFactor] at *
  linarith only [hH,ht]

end
end ASDExplicitGamma.Native
