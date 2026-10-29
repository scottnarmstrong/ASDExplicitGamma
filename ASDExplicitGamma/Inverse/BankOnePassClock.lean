module

public import ASDExplicitGamma.Gaussian.ShellFrameClock
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Inverse.BankHistoryProfileArithmetic
public import ASDExplicitGamma.Statements.NativeInductionState

/-! The one-pass uniform shell clock and final true-frame restoration. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Inverse

noncomputable def bankOnePassFrame (M : ABKModel 2) : ℝ :=
  (1-(11/5:ℝ)*40*M.gamma)⁻¹

theorem bank_one_pass_frame_pos (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    0 < bankOnePassFrame M := by
  have hh : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  unfold bankOnePassFrame
  apply inv_pos.mpr
  linarith only [hh]

/-- The true frame is restored only after all forty shells have been inserted. -/
theorem bank_one_pass_frame_restoration (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (k : ℤ) :
    (Annealed.sigmaBar M (k+40):ℝ)/(Annealed.sigmaBar M k:ℝ) ≤ bankOnePassFrame M := by
  have hc := (Scalar.sigmaBar_structural_continuity_nat M k 40).2
  have hh : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
  have hd : (11/10:ℝ)*(2*M.gamma*40) < 1 := by linarith only [hh]
  have hb := inv_three_power_bound (2*M.gamma*40)
    (mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le) (by norm_num)) hd
  have hb' : (3:ℝ)^(2*M.gamma*40) ≤ bankOnePassFrame M := by
    convert hb using 1
    simp only [bankOnePassFrame, one_div]
    congr 1
    ring
  exact hc.trans hb'

/-- The 0.49 corridor pays every shell against the same clock. The coefficient
sum is left unweighted; no shell growth factor is inserted into that sum. -/
theorem bank_one_pass_shell_clock (M : ABKModel 2) (h : ℝ)
    (hg : M.gamma ≤ gammaZero) (k i : ℤ) (hi : i ≤ k+40)
    (hlower : (49/100:ℝ)*shellVarianceSum h M.gamma k ≤
      (Annealed.sigmaBar M k:ℝ)^2) :
    q3ModelAmplitude M h i ^ 2 / (Annealed.sigmaBar M k:ℝ)^2 ≤
      (9/2:ℝ)*M.gamma*bankOnePassFrame M := by
  have hγ := M.shellPrefix.gamma_pos
  let δ := 1-(3:ℝ)^(-(2*M.gamma))
  have hδ : 0 < δ := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (mul_pos (by norm_num) M.shellPrefix.gamma_pos)))
  have hδbound : δ ≤ (9/2:ℝ)*(49/100)*M.gamma := by
    have he := Real.add_one_le_exp (-(2*M.gamma)*Real.log 3)
    have hc := mul_le_mul_of_nonneg_right Numerics.Scalar.lower_clock_margins.2.le
      M.shellPrefix.gamma_pos.le
    dsimp [δ]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
    rw [mul_comm (Real.log 3)]
    linarith only [he,hc]
  have hs := (Annealed.sigmaBar_characterization M k).1
  have hbase : h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)) ≤
      (Annealed.sigmaBar M k:ℝ)^2*(δ/(49/100:ℝ)) := by
    have hb : (49/100:ℝ)*(h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))) ≤
        (Annealed.sigmaBar M k:ℝ)^2*δ := by
      apply (div_le_iff₀ hδ).mp
      simpa only [shellVarianceSum, δ, mul_div_assoc] using hlower
    linarith only [hb]
  have hexp : (3:ℝ)^(2*M.gamma*(i:ℝ)) =
      (3:ℝ)^(2*M.gamma*(k:ℝ))*(3:ℝ)^(2*M.gamma*((i:ℝ)-k)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  have hgrowth : (3:ℝ)^(2*M.gamma*((i:ℝ)-k)) ≤ bankOnePassFrame M := by
    have hiR : (i:ℝ)-(k:ℝ) ≤ 40 := by exact_mod_cast (show i-k ≤ 40 by omega)
    have hm := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (mul_le_mul_of_nonneg_left hiR (by positivity : 0 ≤ 2*M.gamma))
    have hh : M.gamma ≤ 17/50000 := by simpa [gammaZero] using hg
    have hd : (11/10:ℝ)*(2*M.gamma*40) < 1 := by linarith only [hh]
    have hb := inv_three_power_bound (2*M.gamma*40) (by positivity) hd
    have hb' : (3:ℝ)^(2*M.gamma*40) ≤ bankOnePassFrame M := by
      convert hb using 1
      simp only [bankOnePassFrame, one_div]
      congr 1
      ring
    exact hm.trans hb'
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [q3ModelAmplitude_sq,hexp,← mul_assoc]
  calc
    _ ≤ ((Annealed.sigmaBar M k:ℝ)^2*(δ/(49/100:ℝ)))*
        (3:ℝ)^(2*M.gamma*((i:ℝ)-k)) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ ≤ ((Annealed.sigmaBar M k:ℝ)^2*((9/2:ℝ)*M.gamma))*
        (3:ℝ)^(2*M.gamma*((i:ℝ)-k)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith only [hδbound]
    _ ≤ ((Annealed.sigmaBar M k:ℝ)^2*((9/2:ℝ)*M.gamma))*bankOnePassFrame M :=
      mul_le_mul_of_nonneg_left hgrowth (by positivity)
    _ = _ := by ring

/-- The native lower coordinate supplies the required 0.49 corridor directly,
including the molecular regime; no variance-to-viscosity comparison is needed. -/
theorem bank_one_pass_native_shell_clock (M : ABKModel 2) (h : ℝ)
    (hg : M.gamma ≤ gammaZero) (k i : ℤ) (hi : i ≤ k+40)
    (hstate : nativeInductionState M h k) :
    q3ModelAmplitude M h i ^ 2 / (Annealed.sigmaBar M k:ℝ)^2 ≤
      (9/2:ℝ)*M.gamma*bankOnePassFrame M := by
  have hγ := M.shellPrefix.gamma_pos
  have hδ : 0 < 1-(3:ℝ)^(-(2*M.gamma)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (mul_pos (by norm_num) hγ)))
  obtain ⟨_,_,_,_,_,_,hlower,_⟩ := hstate
  apply bank_one_pass_shell_clock M h hg k i hi
  have hB : 0 ≤ shellVarianceSum h M.gamma k := by
    unfold shellVarianceSum
    positivity
  have hnu := sq_nonneg M.nu
  linarith only [hlower,hB,hnu]

end ASDExplicitGamma.Inverse
