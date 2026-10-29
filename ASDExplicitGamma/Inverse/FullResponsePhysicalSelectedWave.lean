module

public import ASDExplicitGamma.Inverse.FullResponsePhysicalWaveMoments
public import ASDExplicitGamma.Inverse.FullResponseSelectedWaveFamily
public import ASDExplicitGamma.Inverse.FixedSelectedHeight
public import ASDExplicitGamma.Inverse.BandCoefficient
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Endpoint-compatible selected physical W₀/W₁ for the full response. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The active root-fourth-moment wave has the literal full-row W₀/W₁ bounds,
including N=l-1 and arbitrary deterministic partial-shell weights. -/
theorem full_response_physical_selected_wave_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights k ∧ weights k ≤ 1)
    (layer : ℕ) (j : Fin 2) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let H := rootSelectedHeight M Q .full
    eLpNorm (fun ω => physicalHeightWeightedWave M Q N 377
      (cubeCorner Q 0) (cubeCorner Q 1)
      (fun _ => sourceBandWeights (Q.scale-342) weights) layer j (H ω) ω)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (physicalSelectedWaveBudget M.gamma p 377 j) := by
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  have hprotected : ∀ k ≤ Q.scale-(377:ℤ)+40, nativeInductionState M h k := by
    intro k hk
    apply hpast k
    omega
  exact full_response_selected_wave_family_Lp M h hM hg Q 377 (by norm_num)
    (rootTau .full) (by norm_num [rootTau]) (rootWaveTuple .full)
    (rootQ .full) hq0 hq hraw hprotected j
    (physicalHeightWeightedWave M Q N 377 (cubeCorner Q 0) (cubeCorner Q 1)
      (fun _ => sourceBandWeights (Q.scale-342) weights) layer j)
    (physical_height_weighted_wave_measurable M Q N 377 _ _ _ layer j)
    (fun H hH r hr => full_response_height_weighted_wave_Lp M h hM Q N hN 377
      (by norm_num) hprotected _ _ _ (fun hk => source_band_weights_bounds _ _ N weights hw)
      layer j H hH r hr) p hp hp256

end
end ASDExplicitGamma.Inverse
