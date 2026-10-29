module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCoefficient
public import ASDExplicitGamma.Gaussian.Q3ModelCovariance
public import ASDExplicitGamma.Triadic.DiagInterpolant

/-! The actual source mesh and exact per-shell bank scale ratios. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

def pureFluxBankSourceDepth (s : ℕ) : ℕ := 5-s

theorem pureFlux_bank_source_depth_le_four (s : ℕ) (hs : 1 ≤ s) :
    pureFluxBankSourceDepth s ≤ 4 := by unfold pureFluxBankSourceDepth; omega

private theorem pureFlux_bank_length_ratio (k : ℤ) (s : ℕ) :
    cubeScaleFactor (originCube 2 k)/(q3ModelLength (k+(s:ℤ))).1 = (1/3:ℝ)^s := by
  simp only [cubeScaleFactor_originCube, q3ModelLength,
    zpow_add₀ (by norm_num : (3:ℝ) ≠ 0), zpow_natCast]
  rw [div_mul_eq_div_div, div_self (zpow_ne_zero k (by norm_num : (3:ℝ) ≠ 0)),
    one_div, one_div_pow]
  rw [one_div]

theorem pureFlux_bank_source_rho (k : ℤ) (s : ℕ) (hs : 1 ≤ s) :
    cubeScaleFactor (originCube 2 k)/(q3ModelLength (k+(s:ℤ))).1 =
      pureFluxCovarianceRho 0 (s-1) := by
  rw [pureFlux_bank_length_ratio]
  unfold pureFluxCovarianceRho
  congr 1
  omega

theorem pureFlux_bank_source_delta (k : ℤ) (s : ℕ) (hs : 1 ≤ s) :
    diagMeshRadius (originCube 2 k) (pureFluxBankSourceDepth s)/
        (q3ModelLength (k+(s:ℤ))).1 = pureFluxCovarianceDelta 0 (s-1) := by
  have hratio : diagMeshRadius (originCube 2 k) (pureFluxBankSourceDepth s)/
      (q3ModelLength (k+(s:ℤ))).1 = (1/3:ℝ)^(s+pureFluxBankSourceDepth s) := by
    unfold diagMeshRadius
    calc
      _ = (cubeScaleFactor (originCube 2 k)/(q3ModelLength (k+(s:ℤ))).1)/
          (3:ℝ)^pureFluxBankSourceDepth s := by ring
      _ = _ := by
        rw [pureFlux_bank_length_ratio]
        simp only [div_eq_mul_inv, one_mul, inv_pow, pow_add]
  rw [hratio]
  unfold pureFluxCovarianceDelta
  rw [← pureFlux_bank_source_rho k s hs, pureFlux_bank_length_ratio]
  by_cases hsmall : s ≤ 5
  · have hexp : s+pureFluxBankSourceDepth s = 5 := by unfold pureFluxBankSourceDepth; omega
    rw [hexp]
    have hp : (1/3:ℝ)^5 ≤ (1/3:ℝ)^s :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hsmall
    norm_num only [show (1/3:ℝ)^5 = 1/243 by norm_num] at hp ⊢
    exact (min_eq_left hp).symm
  · have hm : pureFluxBankSourceDepth s = 0 := by unfold pureFluxBankSourceDepth; omega
    rw [hm, add_zero]
    have hp : (1/3:ℝ)^s ≤ (1/3:ℝ)^5 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num only [show (1/3:ℝ)^5 = 1/243 by norm_num] at hp
    exact (min_eq_right hp).symm

end
end ASDExplicitGamma.Inverse
