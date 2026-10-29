module

public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovExpect
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovMajorant
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovMajorantExp
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovCorrector
public import ASDExplicitGamma.Main.HotCovPathwise
public import ASDExplicitGamma.Main.HotPatchBank
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop

/-! MA-E-COVARIANCE: pathwise domination of the affine carrier at the observer root by an
integrable majorant. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem hotCov_scale_arith_Th (m : ℤ) (hobs : ℕ) :
    cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 =
      (q3ModelLength (m + 1)).1 := by
  rw [cubeScaleFactor_originCube, q3ModelLength, ← zpow_natCast (3 : ℝ) (hobs + 5),
    ← zpow_natCast (3 : ℝ) 6, ← zpow_sub₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  congr 1
  push_cast
  ring

theorem hotCov_hL_obs_Th (m : ℤ) (hobs : ℕ) :
    ∀ R ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5),
      cubeScaleFactor R * 3 ^ 6 ≤ (q3ModelLength (m + 1)).1 := by
  intro R hR
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR]
  exact (hotCov_scale_arith_Th m hobs).le

theorem hotCov_hmesh_obs_Th (m : ℤ) (hobs : ℕ) :
    diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) * 3 ^ 6 ≤
      (q3ModelLength (m + 1)).1 :=
  (hotCov_scale_arith_Th m hobs).le

/-- The trace defect appearing in the paired Bessel bound is the observer energy drop. -/
theorem hotCov_delta_eq_drop_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    descendantsAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (hotCovObsCoef_Th M m hobs t ω)) 1) -
      traceDefect (openCubeSet (originCube 2 (m + hobs)))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (hotCovObsCoef_Th M m hobs t ω)) 1 = mainHotDropObs_Th M m hobs t ω := by
  unfold mainHotDropObs_Th descendantsAverage
  have hroot := main_hot_trace_eq_frame_trace_obs_Th M m (originCube 2 (m + hobs)) t ω 0
    (originCube 2 (m + hobs)) (by simp)
  rw [hroot]
  simp only []
  congr 2
  refine Finset.sum_congr rfl fun U hU => ?_
  exact (main_hot_trace_eq_frame_trace_obs_Th M m (originCube 2 (m + hobs)) t ω (hobs + 5) U hU).symm

/-- `Xk <= B * Delta`: the potential energy is paid by the paired Bessel budget. -/
theorem hotCov_Xk_le_Th (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (B : ℝ)
    (hB : ∀ U ∈ descendantsAtDepth Q d,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    ∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
      (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad ≤
      B * (descendantsAverage Q d (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1) := by
  classical
  have hpaired := hot_cov_paired_drop_weak Q d nu sigma hnu hsigma k B hB
  have hsplit : (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
      vectorWeakHaarEnergy U.val (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential +
      vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c)))) =
      (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U => vectorWeakHaarEnergy U.val
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential)) +
      ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))) := by
    simp only [old_signed_cell_average_add, Finset.sum_add_distrib]
  have hYk0 : 0 ≤ ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
      vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))) :=
    Finset.sum_nonneg (fun c _ =>
      old_signed_cell_average_mono Q d (f := fun _ => 0) (fun U => vectorWeakHaarEnergy_nonneg _ _)
        |>.trans' (by simp [oldSignedCellAverage]))
  rw [hotCov_Xk_eq]
  rw [hsplit] at hpaired
  linarith

/-- The integrable majorant of the affine carrier at the observer root. -/
def hotCovGObs_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (b ^ 2 / 2) * (mixedBridgeBstar M m t ω * mainHotDropObs_Th M m hobs t ω) +
  2 * Real.sqrt (mixedBridgeBstar M m t ω * mainHotDropObs_Th M m hobs t ω) *
    Real.sqrt (hotCovPE_Th M m hobs t b (q3ModelLength (m + 1)) ω) +
  2 * (mainKrem (b ^ 2) * Real.sqrt (mixedBridgeBstar M m t ω *
        mainHotDropObs_Th M m hobs t ω) +
      mainKd (b ^ 2) * Real.sqrt (mainHotObsVl2_Th M m hobs t ω)) *
    Real.sqrt (∑ c : BlockCoord 2, hotCovPA_Th M m hobs t b (q3ModelLength (m + 1)) c ω)

/-- PATHWISE: the affine carrier of the hot trial at the observer root is below `hotCovGObs_Th`. -/
theorem hotCov_pathwise_obs_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) (ω : Cutoff.CutoffSample 2) :
    hotCovAffCarrier (originCube 2 (m + hobs)) (hobs + 5) M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1 (hotCovObsCoef_Th M m hobs t ω) b
      (q3ModelLength (m + 1)) ≤ hotCovGObs_Th M m hobs t b ω := by
  classical
  have hB : ∀ U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5),
      lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ) (hotCovObsCoef_Th M m hobs t ω)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        mixedBridgeBstar M m t ω :=
    fun U hU => hot_cell_history_le_bstar M m hobs h40 t ht ω U hU
  have hp := hot_cov_pathwise_bound (originCube 2 (m + hobs)) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (hotCovObsCoef_Th M m hobs t ω) b (q3ModelLength (m + 1))
    (hotCov_hL_obs_Th m hobs) (hotCov_hmesh_obs_Th m hobs) _ hB
  rw [hotCov_delta_eq_drop_Th] at hp
  have hX := hotCov_Xk_le_Th (originCube 2 (m + hobs)) (hobs + 5) M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (hotCovObsCoef_Th M m hobs t ω) _ hB
  rw [hotCov_delta_eq_drop_Th] at hX
  have hV := hotCov_vphi_eq_Th M m hobs t ω
  have hK := hotCov_ke2_le_pe_Th M m hobs t b (q3ModelLength (m + 1)) ω
  have hA := hotCov_kaff2_le_pa_Th M m hobs t b (q3ModelLength (m + 1)) ω
  have hk1 := mainKrem_nonneg (b ^ 2)
  have hk2 := mainKd_nonneg (b ^ 2)
  refine hp.trans ?_
  unfold hotCovGObs_Th
  rw [hV]
  have s1 := Real.sqrt_le_sqrt hX
  have s2 := Real.sqrt_le_sqrt hK
  have s3 := Real.sqrt_le_sqrt hA
  gcongr

end

end ASDExplicitGamma.Main
