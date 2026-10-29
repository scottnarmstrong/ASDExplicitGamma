module

public import ASDExplicitGamma.Inverse.StoppedQ3Marks
public import ASDExplicitGamma.Inverse.StoppedMarkControl
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! The native protected past supplies the two literal q3 mark probabilities. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Exact conversion of the physical shell label exponent to the block side. -/
theorem positive_label_power (n : ℕ) :
    (3:ℝ)^((3/2:ℝ)*((n:ℝ)+1)) =
      positiveLabelSide n*Real.sqrt (positiveLabelSide n) := by
  unfold positiveLabelSide
  rw [Real.sqrt_eq_rpow,← Real.rpow_natCast 3 (n+1),← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
    ← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  congr 1
  push_cast
  ring

/-- The zero mark rarity is derived from the literal history coordinate at
the three earlier buffered labels; no bad-event probability is assumed. -/
theorem q3_local_probability_of_native (M : ABKModel 2) (h : ℝ)
    (hg : M.gamma ≤ gammaZero) (j : ℤ) (τ η : ℝ) (hτ : 0 < τ)
    (hpast : ∀ k ≤ j+40, nativeInductionState M h k) (x : BlockSite) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real ((q3PlanarMarks M j τ η).localMark x) ≤
      (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 := by
  apply q3_local_mark_probability M hg j τ η hτ x
  intro i
  have hl := elementary_cube_scale_le j x i
  exact (hpast _ (by omega)).2.2.2.1

/-- The source Gaussian wave gate supplies every positive raw mark rate from
the protected ordinary native past, in each member's true old frame. -/
theorem q3_positive_probability_of_native (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero) (j : ℤ) (τ : ℝ)
    (t : WaveGateTuple) (hpast : ∀ k ≤ j+40, nativeInductionState M h k)
    (n : ℕ) (x : BlockSite) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
      ((q3PlanarMarks M j τ (waveGateEta t)).positiveMark n x) ≤
      Real.exp (-1200*positiveLabelSide n*Real.sqrt (positiveLabelSide n)) := by
  have hh := q3_positive_mark_probability M h hM hg j τ t n x (fun i =>
    wave_gate_lower_corridor M h _ (hpast _ (by
      have hl := elementary_cube_scale_le j x i
      omega)))
  rw [positive_label_power] at hh
  simpa only [mul_assoc] using! hh

end
end ASDExplicitGamma.Inverse
