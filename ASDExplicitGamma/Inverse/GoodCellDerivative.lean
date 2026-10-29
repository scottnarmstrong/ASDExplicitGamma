module

public import ASDExplicitGamma.Inverse.LaterBandDerivative
public import ASDExplicitGamma.Inverse.WaveGateSeries
public import ASDExplicitGamma.Inverse.StoppedBadCellLift

/-! The actual source good-cell event supplies the actual later-band
sensitivity derivative size, including all later shells before the UV cutoff. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Goodness supplies every later derivative threshold in the same true frame. -/
theorem good_cell_wave_gate (M : ABKModel 2) (Q : TriadicCube 2) (τ η : ℝ)
    (ω : Cutoff.CutoffSample 2) (hgood : ω ∉ cellFailure M τ η Q) (k : ℤ) (hk : Q.scale+40 < k) :
    waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) (Annealed.sigmaBar M (Q.scale+40):ℝ) (ω.val k) ≤
      η*(3:ℝ)^(-((k-(Q.scale+40):ℤ):ℝ)/8) := by
  let L := (k-(Q.scale+40)-1).toNat
  have hL : Q.scale+40+(L+1:ℕ)=k := by dsimp only [L]; omega
  have he : (L:ℝ)+1=((k-(Q.scale+40):ℤ):ℝ) := by
    have hi : (L:ℤ)+1=k-(Q.scale+40) := by dsimp only [L]; omega
    exact_mod_cast hi
  have hh : waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q)
      (Annealed.sigmaBar M (Q.scale+40):ℝ) (ω.val (Q.scale+40+(L+1:ℤ))) ≤
        η*(3:ℝ)^(-((L:ℝ)+1)/8) := by
    by_contra hn
    exact hgood (Or.inr ⟨L,lt_of_not_ge hn⟩)
  have hL' : Q.scale+40+(L+1:ℤ)=k := by omega
  rwa [hL',he] at hh

/-- The actual finite band obeys the complete source derivative budget on
its actual good cell. There is no derivative-size premise. -/
theorem good_cell_later_band_Dsharp (M : ABKModel 2) (Q : TriadicCube 2) (τ η : ℝ)
    (hη : 0 ≤ η) (ω : Cutoff.CutoffSample 2) (hgood : ω ∉ cellFailure M τ η Q)
    (J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale+40) J, 0 ≤ weights k ∧ weights k ≤ 1) :
    sensitivityDsharp Q (laterBandW2 Q (Q.scale+40) J weights ω) ≤
      (Annealed.sigmaBar M (Q.scale+40):ℝ)*(10*η) := by
  let σ := (Annealed.sigmaBar M (Q.scale+40):ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M _).1
  have hsum : (∑ k ∈ Finset.Ioc (Q.scale+40) J, |weights k| *
      waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k)) ≤ 10*η := by
    calc
      _ ≤ ∑ k ∈ Finset.Ioc (Q.scale+40) J, η*(3:ℝ)^(-((k-(Q.scale+40):ℤ):ℝ)/8) := by
        apply Finset.sum_le_sum
        intro k hk
        have hgate := good_cell_wave_gate M Q τ η ω hgood k (Finset.mem_Ioc.mp hk).1
        have h0 : 0 ≤ waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k) := by
          unfold waveGateDerivativeSize
          have hs := (Homogenization.cubeScaleFactor_pos' Q).le
          positivity
        rw [abs_of_nonneg (hw k hk).1]
        exact (mul_le_of_le_one_left h0 (hw k hk).2).trans hgate
      _ = η*∑ k ∈ Finset.Ioc (Q.scale+40) J, (3:ℝ)^(-((k-(Q.scale+40):ℤ):ℝ)/8) := by rw [Finset.mul_sum]
      _ ≤ η*10 := mul_le_mul_of_nonneg_left (wave_gate_interval_threshold_sum_le_ten _ _) hη
      _ = _ := mul_comm _ _
  exact (later_band_Dsharp_le_wave_sum Q (Q.scale+40) J weights ω σ hσ).trans
    (mul_le_mul_of_nonneg_left hsum hσ.le)

end
end ASDExplicitGamma.Inverse
