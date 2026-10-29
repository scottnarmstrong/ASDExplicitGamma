module

public import ASDExplicitGamma.Inverse.AllOrderStoppedGeometry
public import ASDExplicitGamma.Inverse.PhysicalGaussianAllOrderTail
public import ASDExplicitGamma.Inverse.PhysicalGaussianHeightWave
public import ASDExplicitGamma.Inverse.StoppedSelectedWaveExactFamily
public import ASDExplicitGamma.Inverse.PhysicalGaussianSelectedWave
public import ASDExplicitGamma.Inverse.PhysicalGaussianCorrelatedSeries
public import ASDExplicitGamma.Inverse.SelectedGaussian
public import ASDExplicitGamma.Inverse.CorrelatedSeries
public import ASDExplicitGamma.Gaussian.WaveGatePhysicalMean
public import ASDExplicitGamma.Gaussian.WaveGatePowerIdentities

/-! Physical derivative supremum, exact selected tails and complete correlated errors. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The Gaussian step: exact selected physical waves at every moment
order on the same band, complete correlated-error sums before selection,
and the actual selected-height tail. The derivative mean and gate are the
two preceding exports of this module. -/
theorem physical_gaussian_tails (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ)
    (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc
      (physicalResetOldLabel Q (heightEntrance (orderBand p)) hk) N,
      0 ≤ weights hk k ∧ weights hk k ≤ 1) :
    let H0 := heightEntrance (orderBand p)
    let H := q3SelectedHeight M Q (orderBand p)
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    (∀ (layer : ℕ) (j : Fin 2) (r : ℝ), 2 ≤ r →
      eLpNorm (fun ω => physicalHeightWeightedWave M Q N H0 a c weights layer j (H ω) ω)
        (ENNReal.ofReal r) μ ≤ ENNReal.ofReal (physicalSelectedWaveExactBudget M.gamma r H0 j)) ∧
    (∀ j : Fin 2,
      (∀ᵐ ω ∂μ, Summable (fun hk =>
        ‖correlatedDensityTerm M Q N p (2700*(3:ℝ)^80) a c weights j hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk,
        correlatedDensityTerm M Q N p (2700*(3:ℝ)^80) a c weights j hk ω)
        (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (40*(2*p+2)*bandDensitySum4 (orderBand p) M.gamma
          (2700*(3:ℝ)^80) (H0-38) j)) ∧
    (∀ t : ℕ, H0 ≤ t → μ.real {ω | t < H ω} ≤ Real.exp (-heightExponent t/32)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro layer j r hr
    exact selected_physical_wave_Lp M h hM hγ Q p hp hpast N hN
      a c weights hw layer j r hr
  · intro j
    exact correlated_density_series_Lp M h hM hγ Q p hp hpast N hN
      a c weights hw (2700*(3:ℝ)^80) (by positivity) j
  · intro t ht
    exact q3_selected_height_tail_at_order M h hM hγ Q p hp hpast t ht

end
end Inverse
