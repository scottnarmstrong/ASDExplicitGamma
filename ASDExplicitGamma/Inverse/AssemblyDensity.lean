module

public import ASDExplicitGamma.Inverse.GaussianTails
public import ASDExplicitGamma.Inverse.RootErrorMeasurable

/-! All-order density bounds for the actual three geometric resolutions. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The uniform-density producer at the actual mark label of each
geometric resolution. The five generations in the geometry keep
every such old label inside the protected native past. -/
theorem assembly_geometric_density_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (k H0 : ℕ) (hH0 : heightEntrance k+5 ≤ H0)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (p : ℝ) (hp : 2 ≤ p) (m : ℕ) (hm : m=2 ∨ m=4)
    (hk : ℕ × ℕ) (e : Fin 3) :
    eLpNorm (resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
      (allOrderDensity:ℝ) 1324 m hk e) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (uniformDensityPowerEnvelope m p (resetDensityDepth H0 hk e)) := by
  let R := resetDensityDepth H0 hk e
  let j := rootFineLabel Q R
  let E := localizationWhitneyLayer Q (H0+hk.1) hk.2
  have h333 : 333 ≤ H0 := by unfold heightEntrance at hH0; omega
  have hR : H0-40 ≤ R := (reset_density_depth_lower H0 h333 hk e).2
  have hpast' : ∀ n ≤ j+40, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    unfold j rootFineLabel at hn
    unfold heightEntrance at hH0
    omega
  have hτ : 0 < resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hq0 : 0 ≤ (allOrderDensity:ℝ) :=
    ((Real.exp_pos _).trans all_order_density_floor).le
  have hE : MeasurableSet E := localization_whitney_layer_measurable Q _ _
  have hEQ : E ⊆ cubeSet Q := localization_whitney_layer_subset Q _ _
  have hv : (volume E).toReal/(volume (cubeSet Q)).toReal = bankLayerWeight hk.2 :=
    localization_whitney_layer_volume Q _ _
  have hv1 : bankLayerWeight hk.2 ≤ 1 := by
    rw [← hv]
    exact (root_layer_fraction_bounds Q E hEQ).2
  have hb := q3_root_spatial_density_uniform_Lp M h hM hγ j
    resetAllOrderTau hτ .allOrder (allOrderDensity:ℝ) hq0
    all_order_density_small all_order_density_floor.le
    all_order_density_covers_raw hpast' 1324 (by norm_num)
    all_order_density_moment_cutoff Q R m hm p hp E hE hEQ
  dsimp only at hb
  rw [hv] at hb
  have hb' : eLpNorm (resetDensityExcess M Q H0 resetAllOrderTau
      (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 m hk e)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (uniformDensityBudget m p (R/6+1)
          ((1/9:ℝ)^R) (bankLayerWeight hk.2)) := hb.2
  exact hb'.trans (ENNReal.ofReal_le_ofReal
    (uniform_density_budget_source_powers m p (by linarith only [hp]) R _ hv1))

/-- The actual geometric density excess retains the same three band powers
as the density estimates. -/
theorem assembly_geometric_density_band_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (H0 : ℕ) (hH0 : heightEntrance (orderBand p)+5 ≤ H0)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (m : ℕ) (hm : m=2 ∨ m=4) (hk : ℕ × ℕ) (e : Fin 3) :
    eLpNorm (resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
      (allOrderDensity:ℝ) 1324 m hk e) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (bandDensityPowerEnvelope m (orderBand p)
          (resetDensityDepth H0 hk e)) := by
  let k := orderBand p
  let P := bandOrderMajorant k
  have hpP : p ≤ P := order_le_band_majorant p
  have hP : 2 ≤ P := hp.trans hpP
  have hb := assembly_geometric_density_Lp M h hM hγ Q k H0 hH0
    hpast P hP m hm hk e
  have h333 : 333 ≤ H0 := by unfold heightEntrance at hH0; omega
  have hR : bandDensityEntrance k ≤ resetDensityDepth H0 hk e := by
    have hd := (reset_density_depth_lower H0 h333 hk e).2
    unfold bandDensityEntrance heightEntrance at *
    omega
  have hn := eLpNorm_le_eLpNorm_of_exponent_le
    (f := resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
      (allOrderDensity:ℝ) 1324 m hk e)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (ENNReal.ofReal_le_ofReal hpP)
  exact (hn.trans hb).trans (ENNReal.ofReal_le_ofReal
    (uniform_density_envelope_le_band m k _ hR))

end
end ASDExplicitGamma.Inverse
