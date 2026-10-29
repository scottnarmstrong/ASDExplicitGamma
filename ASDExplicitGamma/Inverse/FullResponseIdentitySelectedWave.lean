module

public import ASDExplicitGamma.Inverse.FullResponseIdentityHeightWave
public import ASDExplicitGamma.Inverse.FullResponseSelectedWaveFamily
public import ASDExplicitGamma.Inverse.FixedSelectedHeight

/-! Correlated selected-height moments of the actual identity-layer shear wave. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The full-row selected identity wave has the same W₀/W₁ budgets as the
physical root wave. All ordinary moments are discharged from the actual
local shear means, with the exact layer fraction retained. -/
theorem full_response_identity_selected_wave_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights k ∧ weights k ≤ 1)
    (layer : ℕ) (j : Fin 2) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let H := rootSelectedHeight M Q .full
    eLpNorm (fun ω => fullResponseIdentityWeightedWave M Q N weights layer j (H ω) ω)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (physicalSelectedWaveBudget M.gamma p 377 j) := by
  have hprotected : ∀ n ≤ Q.scale-342, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    omega
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  exact full_response_selected_wave_family_Lp M h hM hg Q 377 (by norm_num)
    (rootTau .full) (by norm_num [rootTau]) (rootWaveTuple .full)
    (rootQ .full) hq0 hq hraw (by
      intro k hk
      apply hpast k
      omega) j
    (fullResponseIdentityWeightedWave M Q N weights layer j)
    (full_response_identity_weighted_wave_measurable M h hM Q hprotected N hN weights hw layer j)
    (fun H hH r hr => (full_response_identity_weighted_wave_Lp M h hM Q hprotected
      N hN weights hw layer j H hH r (by linarith only [hr])).2) p hp hp256

end
end ASDExplicitGamma.Inverse
