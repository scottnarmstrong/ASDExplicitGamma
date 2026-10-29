module

public import ASDExplicitGamma.Main.HotObsEnvelope
public import ASDExplicitGamma.Main.EnvelopeSigns

/-! MA-E-COVARIANCE: positivity of the actual envelope `xi` used in the proxy payments. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Numerics.MainReturn
  Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem hotCov_xi_nonneg (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ mainEnvelopeXi
      ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
      M.gamma mainSourceInversePrefix (theta M) t := by
  have hprefixQ : (140120486781 / 1000000000000 : ℚ) ≤
      observer1Panel0Data.initialInverseMean - (1 / 10 ^ 12 : ℚ) := by
    decide +kernel
  have hprefix : (140120486781 / 1000000000000 : ℝ) ≤ mainSourceInversePrefix := by
    change (140120486781 / 1000000000000 : ℝ) ≤
      (observer1Panel0Data.initialInverseMean : ℝ) - (1 / 10 ^ 12 : ℝ)
    have hprefixR := (Rat.cast_le (K := ℝ)).2 hprefixQ
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_one] using hprefixR
  have hge := mainEnvelopeXi_ge_initial (v := (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2) (gamma := M.gamma) (xiPre := mainSourceInversePrefix)
    (theta := theta M) (t := t) (sq_nonneg _) M.shellPrefix.gamma_pos.le hγ
    (ASDExplicitGamma.Cold.cold_theta_pos M).le ht.1
  linarith [hprefix]

end

end ASDExplicitGamma.Main
