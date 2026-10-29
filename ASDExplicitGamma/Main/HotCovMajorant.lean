module

public import ASDExplicitGamma.Main.HotCovExpect
public import ASDExplicitGamma.Main.HotCovMeanSize

/-! MA-E-COVARIANCE, expectation step 4: the integrable proxy majorants of `KE2` and `Kaff2`
and their expectations: `E KE2 <= (xi/2)(e_+^2 + e_-^2)`, `E Kaff2 <= (xi/2)(2 v + B0/2)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Frame proxy of the cell's own skew coefficient. -/
def hotCovSkewProxy (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2) (e : Vec 2) : ℝ :=
  oldSignedDirectionalProxy U (responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) e

/-- The proxy majorant of `KE2`. -/
def hotCovPE (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
    ∑ c : BlockCoord 2, hotCovSkewProxy M m t ω U.val
      (hotCovErrCol (originCube 2 (m + hobs)) U.val b L (hotCovPlusC c) (hotCovIdxC c)))

/-- The proxy majorant of `Kaff2`, load by load. -/
def hotCovPA (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (c : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldSignedCellAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
    ∑' n : whiteBasisIndex, hotCovSkewProxy M m t ω U.val
      (hotCovFlatMeanVec (originCube 2 (m + hobs)) b L (hotCovPlusC c) U.val n (hotCovIdxC c)))

theorem hotCov_ke2_le_pe (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : Cutoff.CutoffSample 2) :
    hotCovKE2 (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (hotCovObsCoef M m hobs t ω) b L ≤
    hotCovPE M m hobs t b L ω := by
  unfold hotCovKE2 hotCovPE
  refine old_signed_cell_average_mono _ _ fun U => Finset.sum_le_sum fun c _ => ?_
  refine (hotCov_rcvC_weak_le _ _ _ _ _ _ _ c U _).trans (le_of_eq ?_)
  exact hotCov_proxy_cell_bridge M _ _ m t ω U _

theorem hotCov_kaff2_le_pa (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : Cutoff.CutoffSample 2) :
    hotCovKaff2 (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (hotCovObsCoef M m hobs t ω) b L ≤
    ∑ c : BlockCoord 2, hotCovPA M m hobs t b L c ω := by
  unfold hotCovKaff2 hotCovPA oldSignedCellAverage
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine le_trans (Finset.sum_le_sum fun U _ => Finset.sum_le_sum fun c _ => ?_)
    (le_of_eq Finset.sum_comm)
  have hs := hotCov_proxy_family_summable U.val M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (hotCovCellCoef _ _ (hotCovObsCoef M m hobs t ω) U)
    (fun n => hotCovFlatMeanVec (originCube 2 (m + hobs)) b L (hotCovPlusC c) U.val n
      (hotCovIdxC c))
    (hotCov_flat_mean_vec_sq_summable _ _ b L (hotCovPlusC c) U.val U.property _)
  have hle (n : whiteBasisIndex) := (hotCov_rcvC_weak_le (originCube 2 (m + hobs))
    (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (hotCovObsCoef M m hobs t ω) c U
    (hotCovFlatMeanVec (originCube 2 (m + hobs)) b L (hotCovPlusC c) U.val n (hotCovIdxC c)))
  have hK : Summable (fun n : whiteBasisIndex => vectorWeakHaarEnergy U.val
      (hotCovRcvC (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (hotCovObsCoef M m hobs t ω) c U
        (hotCovFlatMeanVec (originCube 2 (m + hobs)) b L (hotCovPlusC c) U.val n
          (hotCovIdxC c)))) :=
    hs.of_nonneg_of_le (fun n => vectorWeakHaarEnergy_nonneg _ _) hle
  refine hK.tsum_le_tsum (fun n => ?_) ?_
  · exact (hle n).trans (le_of_eq (hotCov_proxy_cell_bridge M _ _ m t ω U _))
  · exact hs.congr (fun n => hotCov_proxy_cell_bridge M _ _ m t ω U _)

end

end ASDExplicitGamma.Main
