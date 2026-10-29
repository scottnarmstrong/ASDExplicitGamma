module

public import ASDExplicitGamma.Scalar.SignalInterval
public import ASDExplicitGamma.Scalar.UpperSourceCaps

/-! The upper-cell signal gate, including molecular endpoints. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Algsuperdiff.Section3
noncomputable section

/-- The upper signal gate needs only the earlier mixed lower corridor.
No nonmolecular-target premise is required for this one-sided estimate. -/
theorem upper_cell_signal_le (nu B BN sigma a : ℝ)
    (hs : 0 < sigma) (hB : 0 ≤ B) (hclock : BN=a*B)
    (hau : a < (2113/1000 : ℝ))
    (hl : (31/50 : ℝ)*B+(19/50 : ℝ)*nu^2 ≤ sigma^2) :
    (BN-B)/(2*sigma^2) < (9/10 : ℝ) := by
  have hhi := mul_le_mul_of_nonneg_right hau.le hB
  rw [← hclock] at hhi
  rw [div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) (sq_pos_of_pos hs))]
  nlinarith only [hhi, hl, hB, sq_nonneg nu, sq_pos_of_pos hs]

/-- At the source block length, the actual signal meets the principal gate
using only the native state at its completed left endpoint. -/
theorem upper_cell_sigmaBar_signal_le
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) :
    (shellVarianceSum h M.gamma (n+⌊(17/50:ℝ)/M.gamma⌋)-
      shellVarianceSum h M.gamma n)/
      (2*(Annealed.sigmaBar M n : ℝ)^2) < (9/10 : ℝ) := by
  have hgamma : M.gamma ≤ 17/50000 := hg
  have hclock := signal_clock_ratio M.gamma M.shellPrefix.gamma_pos hgamma
  have hB : 0 ≤ shellVarianceSum h M.gamma n := by
    have hd : 0 < 1-(3:ℝ)^(-(2*M.gamma)) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (neg_neg_of_pos (mul_pos (by norm_num) M.shellPrefix.gamma_pos)))
    exact div_nonneg (mul_nonneg (sq_nonneg h)
      (Real.rpow_nonneg (by norm_num) _)) hd.le
  exact upper_cell_signal_le M.nu _ _ _ _ (Annealed.sigmaBar M n).property hB
    (shellVarianceSum_add h M.gamma n _) hclock.2 hstate.2.2.2.2.2.2.1

end
end ASDExplicitGamma.Scalar
