module

public import ASDExplicitGamma.Inverse.StoppedSelectedClockNorm
public import ASDExplicitGamma.Numerics.Inverse.TailSoundness

/-! Actual selected-root clocks consume the exact 512-factorial tail certificates. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Physical root clock bound at order 256, before the fixed-tuple substitution. -/
theorem selected_root_physical_power_cap (γ z : ℝ) (hg : γ ≤ gammaZero) (hz : 0 ≤ z) :
    (3:ℝ)^((512:ℝ)*γ*z) ≤ Real.exp ((11/10:ℝ)*512*(17/50000)*z) := by
  have hg' : γ ≤ 17/50000 := hg
  have he : (512:ℝ)*γ*z ≤ 512*(17/50000)*z := by
    have hh := mul_le_mul_of_nonneg_right hg' hz
    nlinarith only [hh]
  apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) he).trans
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log 3 ≤ (11/10:ℝ) :=
    (Numerics.log_three_enclosure_30.2).trans (by norm_num)
  have hh := mul_le_mul_of_nonneg_right hl (show 0 ≤ (512:ℝ)*(17/50000)*z by positivity)
  nlinarith only [hh]

/-- Global source first-height moment, with its actual physical clock. -/
theorem selected_global_root_moment_numeric (γ : ℝ) (hg : γ ≤ gammaZero) :
    selectedRootMomentBudget γ 256 333 < (1/10^30:ℝ)^256 := by
  have he : selectedRootMomentBudget γ 256 333 =
      (1000/999:ℝ)*(3:ℝ)^((512:ℝ)*γ*307)*Real.exp (-(3:ℝ)^46/32) := by
    norm_num [selectedRootMomentBudget,selectedFirstClock,heightExponent,Real.rpow_natCast]
  rw [he]
  apply lt_of_le_of_lt _ Numerics.Inverse.inv_global_real_tail
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (selected_root_physical_power_cap γ 307 hg (by norm_num)) (by norm_num : (0:ℝ) ≤ 1000/999))
    (Real.exp_pos (-((3:ℝ)^46/32))).le
  simpa only [neg_div] using! hh

/-- Local/full source first-height moment, with its actual physical clock. -/
theorem selected_local_root_moment_numeric (γ : ℝ) (hg : γ ≤ gammaZero) :
    selectedRootMomentBudget γ 256 377 < (1/10^40:ℝ)^256 := by
  have he : selectedRootMomentBudget γ 256 377 =
      (1000/999:ℝ)*(3:ℝ)^((512:ℝ)*γ*351)*Real.exp (-(3:ℝ)^57/32) := by
    norm_num [selectedRootMomentBudget,selectedFirstClock,heightExponent,Real.rpow_natCast]
  rw [he]
  apply lt_of_le_of_lt _ Numerics.Inverse.inv_local_real_tail
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (selected_root_physical_power_cap γ 351 hg (by norm_num)) (by norm_num : (0:ℝ) ≤ 1000/999))
    (Real.exp_pos (-((3:ℝ)^57/32))).le
  simpa only [neg_div] using! hh

/-- The exact two fixed-tuple tail caps of the source. -/
def selectedRootTiny (H0 : ℕ) : ℝ := if H0=333 then 1/10^30 else 1/10^40

/-- The actual q3 selected root-clock tail is below its source tiny remainder
through real order 256. Lower orders use probability norm monotonicity. -/
theorem q3_selected_root_tail_tiny (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (hg : A.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH : H0=333 ∨ H0=377)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (p : ℝ) (hp256 : p ≤ 256) :
    eLpNorm (selectedRootClockTail A.gamma H0 (q3StoppedHeight A Q H0 τ (waveGateEta t)))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤ ENNReal.ofReal (selectedRootTiny H0) := by
  have hb := q3_selected_root_tail_Lp A h hA hg Q H0 (by omega) τ hτ t q hq0 hq hraw hpast
    256 (by norm_num) (by norm_num)
  have hnum : selectedRootMomentBudget A.gamma 256 H0 ≤ (selectedRootTiny H0)^256 := by
    rcases hH with rfl | rfl
    · simpa only [selectedRootTiny,ite_true] using (selected_global_root_moment_numeric A.gamma hg).le
    · simpa only [selectedRootTiny,show ¬(377:ℕ)=333 by decide,ite_false] using
        (selected_local_root_moment_numeric A.gamma hg).le
  have hroot : (selectedRootMomentBudget A.gamma 256 H0)^(1/256:ℝ) ≤ selectedRootTiny H0 := by
    rw [one_div,Real.rpow_inv_le_iff_of_pos
      (by unfold selectedRootMomentBudget; positivity)
      (by unfold selectedRootTiny; split <;> positivity) (by norm_num : (0:ℝ) < 256)]
    simpa only [Real.rpow_ofNat] using hnum
  have hsmall := hb.trans (ENNReal.ofReal_le_ofReal hroot)
  apply le_trans _ hsmall
  exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hp256)

end
end ASDExplicitGamma.Inverse
