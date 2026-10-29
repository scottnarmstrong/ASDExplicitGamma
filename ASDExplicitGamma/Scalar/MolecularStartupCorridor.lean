module

public import ASDExplicitGamma.Scalar.MolecularUpperFiveFour
public import ASDExplicitGamma.Scalar.MolecularStartupScale

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Algsuperdiff.Section3

/-- The frozen scalar corridor follows from the actual molecular estimates
at each startup label, without any native-state premise. -/
theorem molecular_startup_scalar_corridor (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (n : ℤ)
    (hx : shellVarianceSum h M.gamma n / M.nu ^ 2 ≤ theta M / 400) :
    M.nu ≤ (Annealed.sigmaBar M n : ℝ) ∧
    (31 / 50) * shellVarianceSum h M.gamma n + (19 / 50) * M.nu ^ 2 ≤
      (Annealed.sigmaBar M n : ℝ) ^ 2 ∧
    (Annealed.sigmaBar M n : ℝ) ^ 2 ≤
      M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma n := by
  have hg0 : 0 < gammaZero := by norm_num [gammaZero]
  have ht1 : theta M ≤ 1 := (div_le_one hg0).mpr hγ
  have hx1 : shellVarianceSum h M.gamma n / M.nu ^ 2 ≤ 1 := by linarith only [hx, ht1]
  have hBnu : shellVarianceSum h M.gamma n ≤ M.nu ^ 2 :=
    (div_le_one (sq_pos_of_pos M.nu_pos)).mp hx1
  have hden : 0 < 1 - (3 : ℝ) ^ (-(2 * M.gamma)) := by
    have hp := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
      (by have hpos := M.shellPrefix.gamma_pos; linarith : -(2 * M.gamma) < 0)
    linarith only [hp]
  have hB : 0 ≤ shellVarianceSum h M.gamma n := by
    unfold shellVarianceSum
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos (by norm_num) _).le) hden.le
  have hlow := nu_le_sigmaBar M n
  have hs0 : 0 ≤ (Annealed.sigmaBar M n : ℝ) := M.nu_pos.le.trans hlow
  have hsq : M.nu ^ 2 ≤ (Annealed.sigmaBar M n : ℝ) ^ 2 :=
    (sq_le_sq₀ M.nu_pos.le hs0).mpr hlow
  have hu := sigmaBar_sq_le_molecular_five_four M h hM n hBnu
  refine ⟨hlow, ?_, ?_⟩
  · nlinarith only [hBnu, hsq]
  · nlinarith only [hu, hB]

end ASDExplicitGamma.Scalar
