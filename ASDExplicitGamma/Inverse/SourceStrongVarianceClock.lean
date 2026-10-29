module

public import ASDExplicitGamma.Inverse.BankOnePassClock

/-! The native source variance clock at arbitrary future shell height.
True powers of three are retained so the complete raw tail has no rational
exponential-domain restriction. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The 0.62 scalar corridor bounds every shell in the fixed completed frame. -/
theorem source_strong_shell_variance_clock (M : ABKModel 2) (h : ℝ)
    (k i : ℤ)
    (hlower : (31/50:ℝ)*shellVarianceSum h M.gamma k ≤
      (Annealed.sigmaBar M k:ℝ)^2) :
    q3ModelAmplitude M h i ^ 2 / (Annealed.sigmaBar M k:ℝ)^2 ≤
      (18/5:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*((i:ℝ)-k)) := by
  let δ := 1-(3:ℝ)^(-(2*M.gamma))
  have hδ : 0 < δ := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (mul_pos (by norm_num) M.shellPrefix.gamma_pos)))
  have hδbound : δ ≤ (18/5:ℝ)*(31/50)*M.gamma := by
    have he := Real.add_one_le_exp (-(2*M.gamma)*Real.log 3)
    have hc := mul_le_mul_of_nonneg_right (show 2*Real.log 3 ≤ (18/5:ℝ)*(31/50) by
        have hh := Numerics.Scalar.log_three_small.2.le
        linarith only [hh])
      M.shellPrefix.gamma_pos.le
    dsimp [δ]
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
    rw [mul_comm (Real.log 3)]
    linarith only [he,hc]
  have hs := (Annealed.sigmaBar_characterization M k).1
  have hbase : h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)) ≤
      (Annealed.sigmaBar M k:ℝ)^2*(δ/(31/50:ℝ)) := by
    have hb : (31/50:ℝ)*(h^2*(3:ℝ)^(2*M.gamma*(k:ℝ))) ≤
        (Annealed.sigmaBar M k:ℝ)^2*δ := by
      apply (div_le_iff₀ hδ).mp
      simpa only [shellVarianceSum, δ, mul_div_assoc] using hlower
    linarith only [hb]
  have hexp : (3:ℝ)^(2*M.gamma*(i:ℝ)) =
      (3:ℝ)^(2*M.gamma*(k:ℝ))*(3:ℝ)^(2*M.gamma*((i:ℝ)-k)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [q3ModelAmplitude_sq,hexp,← mul_assoc]
  calc
    _ ≤ ((Annealed.sigmaBar M k:ℝ)^2*(δ/(31/50:ℝ)))*
        (3:ℝ)^(2*M.gamma*((i:ℝ)-k)) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ ≤ ((Annealed.sigmaBar M k:ℝ)^2*((18/5:ℝ)*M.gamma))*
        (3:ℝ)^(2*M.gamma*((i:ℝ)-k)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      linarith only [hδbound]
    _ = _ := by ring

/-- The source clock uses the native lower coordinate at the completed
starting label, including its fixed molecular parameter. -/
theorem source_native_strong_shell_variance_clock (M : ABKModel 2) (h : ℝ)
    (k i : ℤ) (hstate : nativeInductionState M h k) :
    q3ModelAmplitude M h i^2/(Annealed.sigmaBar M k:ℝ)^2 ≤
      (18/5:ℝ)*M.gamma*(3:ℝ)^(2*M.gamma*((i:ℝ)-k)) := by
  obtain ⟨_,_,_,_,_,_,hlower,_⟩ := hstate
  apply source_strong_shell_variance_clock M h k i
  have hden : 0 < 1-(3:ℝ)^(-(2*M.gamma)) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (mul_pos (by norm_num) M.shellPrefix.gamma_pos)))
  have hB : 0 ≤ shellVarianceSum h M.gamma k := by unfold shellVarianceSum; positivity
  linarith only [hlower,hB,sq_nonneg M.nu]

end
end ASDExplicitGamma.Inverse
