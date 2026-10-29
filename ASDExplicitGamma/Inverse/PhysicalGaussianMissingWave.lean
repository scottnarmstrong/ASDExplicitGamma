module

public import ASDExplicitGamma.Gaussian.MissingWave

/-! Extended Lp bounds for the actual physical missing-wave statistic in its true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The genuine normalized squared Frobenius spatial L4 missing wave on a
translated side-3^n square, in the old label's true sigmaBar frame. -/
def physicalMissingWave (A : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  wholeRootSpatialStatistic (Annealed.sigmaBar A j) ((3:ℝ)^n)
    (wholeRootModelBand (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n) j N weights ω)

/-- The statistic is exactly the source's ordinary normalized Frobenius integral. -/
theorem physical_missing_wave_eq_frobenius (A : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    physicalMissingWave A j n N a c weights ω =
      normalizedFrobeniusL4Squared (Annealed.sigmaBar A j) ((3:ℝ)^n)
        (wholeRootModelBand (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n) j N weights ω) :=
  (normalizedFrobeniusL4Squared_eq_spatialStatistic _ _ (Annealed.sigmaBar A j).2 (by positivity) _).symm

/-- Ambient measurability of the physical missing-wave observable. -/
theorem physical_missing_wave_measurable (A : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) : Measurable (physicalMissingWave A j n N a c weights) := by
  let K := closedRectangle a (a+(3:ℝ)^n) c (c+(3:ℝ)^n)
  let P : C(K,ℝ) →L[ℝ] SpatialLp4 K := ContinuousMap.toLp 4 (spatialVolume K) ℝ
  have hF : Continuous (wholeRootSpatialStatistic (Annealed.sigmaBar A j) ((3:ℝ)^n) : C(K,ℝ) → ℝ) :=
    continuous_const.mul ((continuous_norm.comp P.continuous).pow 2)
  exact hF.measurable.comp (measurable_modelWeightedBand K (wholeRootShellLabel j N) (wholeRootWeights j N weights))

theorem physical_missing_wave_nonneg (A : ABKModel 2) (j n N : ℤ) (a c : ℝ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : 0 ≤ physicalMissingWave A j n N a c weights ω := by
  unfold physicalMissingWave wholeRootSpatialStatistic
  positivity

/-- An empty later band really gives the zero physical wave. -/
theorem physical_missing_wave_empty (A : ABKModel 2) (j n : ℤ) (a c : ℝ) (weights : ℤ → ℝ) :
    physicalMissingWave A j n j a c weights = 0 := by
  funext ω
  have hlen : wholeRootBandLength j j=0 := by unfold wholeRootBandLength; omega
  have hband : wholeRootModelBand (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n) j j weights ω=0 := by
    unfold wholeRootModelBand modelWeightedBand
    apply Finset.sum_eq_zero
    intro i _
    have hi := i.isLt
    omega
  rw [physicalMissingWave,hband,wholeRootSpatialStatistic]
  simp only [map_zero,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero]
  rfl

/-- Finiteness of the extended norm is proved separately before consuming
any toReal bound; the empty physical band is included. -/
theorem physical_missing_wave_memLp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (j n N : ℤ) (hjN : j ≤ N) (a c : ℝ) (weights : ℤ → ℝ) (p : ℝ) (hp : 2 ≤ p) :
    MemLp (physicalMissingWave A j n N a c weights) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure := by
  rcases lt_or_eq_of_le hjN with hstrict | rfl
  · have hcast : ((wholeRootBandLength j N:ℕ):ℤ)=N-j := by
      dsimp only [wholeRootBandLength]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hstrict.le)
    have hlen : 0 < wholeRootBandLength j N := by omega
    let physicalMissingWaveBandNeZero : NeZero (wholeRootBandLength j N) := ⟨Nat.ne_of_gt hlen⟩
    exact wholeRoot_actualBand_memLp a (a+(3:ℝ)^n) c (c+(3:ℝ)^n) ((3:ℝ)^n) (Annealed.sigmaBar A j)
      (by linarith [zpow_pos (by norm_num : (0:ℝ) < 3) n])
      (by linarith [zpow_pos (by norm_num : (0:ℝ) < 3) n]) A h hA
      (wholeRootShellLabel j N) (wholeRootShellLabel_injective j N) (wholeRootWeights j N weights) hp
  · rw [physical_missing_wave_empty]
    exact memLp_const 0

end
end ASDExplicitGamma.Inverse
