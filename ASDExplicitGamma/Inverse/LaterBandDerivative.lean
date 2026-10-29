module

public import ASDExplicitGamma.Inverse.LaterBandSupremum
public import ASDExplicitGamma.Triadic.SensitivityODENumerics
public import ASDExplicitGamma.Gaussian.WaveGatePhysicalFunctional

/-! Actual finite later-band sensitivity size, paid by its literal
physical same-frame wave-gate derivative sizes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Model
noncomputable section

/-- The source Hessian coefficient is below one at the proved planar constants. -/
theorem sensitivity_kappa_le_one : sensitivityKappaH ≤ 1 := by
  have hC0 : planarC0 ≤ 1/2 := by linarith only [planarC0_decimal_bounds.2]
  have hC1 : planarC1 ≤ 1/2 := by linarith only [planarC1_decimal_bounds.2]
  have h0 : 0 ≤ planarC0 := Real.sqrt_nonneg _
  have h1 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hp : planarC0*planarC1 ≤ 1/4 := by
    have hh := mul_le_mul hC0 hC1 h1 (by norm_num : (0:ℝ) ≤ 1/2)
    norm_num at hh ⊢
    exact hh
  unfold sensitivityKappaH
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2/Real.pi)).mpr
  apply hp.trans
  rw [one_mul,le_div_iff₀ Real.pi_pos]
  have hpi : Real.pi ≤ 4 := by linarith only [ASDExplicitGamma.Numerics.pi_enclosure.2]
  linarith only [hpi]

/-- The actual W^{2,∞} size of the actual band is bounded on the same
sample by the physical shell gates. The frame sigma is fixed throughout. -/
theorem later_band_Dsharp_le_wave_sum (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (σ : ℝ) (hσ : 0 < σ) :
    sensitivityDsharp Q (laterBandW2 Q n J weights ω) ≤
      σ*∑ k ∈ Finset.Ioc n J, |weights k| * waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k) := by
  let h := laterBandW2 Q n J weights ω
  let B1 := ∑ k ∈ Finset.Ioc n J, |weights k| *
    ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖
  let B2 := ∑ k ∈ Finset.Ioc n J, |weights k| *
    ‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2)
      (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖
  have hs : 0 ≤ cubeScaleFactor Q := (Homogenization.cubeScaleFactor_pos' Q).le
  have hD1 : sensitivityD1 Q h ≤ cubeScaleFactor Q*B1 := by
    have hh := mul_le_mul_of_nonneg_left (later_band_gradient_LInf_le Q n J weights ω) hs
    simpa only [sensitivityD1,mul_assoc] using hh
  have hD2 : sensitivityD2 Q h ≤ cubeScaleFactor Q^2*B2 := by
    have hh := mul_le_mul_of_nonneg_left (later_band_hessian_LInf_le Q n J weights ω) (sq_nonneg (cubeScaleFactor Q))
    simpa only [sensitivityD2,mul_assoc] using hh
  have hD20 : 0 ≤ sensitivityD2 Q h := by
    unfold sensitivityD2 planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  calc
    _ ≤ sensitivityD1 Q h+sensitivityD2 Q h :=
      add_le_add le_rfl (mul_le_of_le_one_left hD20 sensitivity_kappa_le_one)
    _ ≤ cubeScaleFactor Q*B1+cubeScaleFactor Q^2*B2 := add_le_add hD1 hD2
    _ = _ := by
      dsimp only [B1,B2]
      simp only [waveGateDerivativeSize,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      field_simp [hσ.ne']

end
end ASDExplicitGamma.Inverse
