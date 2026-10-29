module

public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovXi
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovMajorant
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovMajorantExp
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovNode
public import ASDExplicitGamma.Main.HotCovCS
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplit
public import ASDExplicitGamma.Main.FlatFieldSourceCaps

/-! MA-E-COVARIANCE: expectation of the integrable majorant `hotCovGObs_Th`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem hotCov_pe_nonneg_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : Cutoff.CutoffSample 2) :
    0 ≤ hotCovPE_Th M m hobs t b L ω := by
  unfold hotCovPE_Th oldSignedCellAverage
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => Finset.sum_nonneg fun c _ => ?_)
  exact (old_signed_directional_proxy_nonneg_le U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (mainInsertionSkewCoefficient m t U.val ω) _).1

theorem hotCov_pa_nonneg_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : Cutoff.CutoffSample 2) :
    0 ≤ ∑ c : BlockCoord 2, hotCovPA_Th M m hobs t b L c ω := by
  refine Finset.sum_nonneg fun c _ => ?_
  unfold hotCovPA_Th oldSignedCellAverage
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun U _ => tsum_nonneg fun n => ?_)
  exact (old_signed_directional_proxy_nonneg_le U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (mainInsertionSkewCoefficient m t U.val ω) _).1

end

end ASDExplicitGamma.Main
