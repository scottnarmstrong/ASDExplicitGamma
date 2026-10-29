module

public import ASDExplicitGamma.Inverse.PhysicalGaussianMissingWave

/-! Physical waves on arbitrary observation squares, including N=l-1. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The missing-wave variance clock is independent of observation side length. -/
theorem missing_wave_toReal_le {j n N : ℤ}
    (hstrict : j < N)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hstate : ASDExplicitGamma.nativeInductionState M h j)
    (a c : ℝ) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (eLpNorm (fun ω => wholeRootSpatialStatistic (Annealed.sigmaBar M j)
      ((3 : ℝ) ^ n) (wholeRootModelBand (a := a) (b := a + (3 : ℝ) ^ n)
        (c := c) (d := c + (3 : ℝ) ^ n) j N weights ω))
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure).toReal ≤
      40 * (p + 2) * (M.gamma * (N - j : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) := by
  let R : ℝ := (3 : ℝ) ^ n
  let σ : ℝ := Annealed.sigmaBar M j
  let K := closedRectangle a (a + R) c (c + R)
  let β : Fin (wholeRootBandLength j N) → ℝ := fun i =>
    q3ModelAmplitude M h (wholeRootShellLabel j N i)
  let w : Fin (wholeRootBandLength j N) → ℝ := wholeRootWeights j N weights
  let L : Fin (wholeRootBandLength j N) → {l : ℝ // 0 < l} := fun i =>
    q3ModelLength (wholeRootShellLabel j N i)
  have hjN : j ≤ N := hstrict.le
  have hσ : 0 < σ := (Annealed.sigmaBar M j).2
  have hR : 0 < R := by positivity
  have hA : 0 ≤ M.gamma * (N - j : ℝ) *
      (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)) := by
    have hγ : 0 < M.gamma := M.shellPrefix.gamma_pos
    have hgap : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hjN
    have hgap' : 0 ≤ (N - j : ℝ) := by linarith
    positivity
  have hvar : (∑ i, w i ^ 2 * β i ^ 2) ≤ σ ^ 2 *
      (9 * (M.gamma * (N - j : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ)))) := by
    change (∑ i, weights (wholeRootShellLabel j N i) ^ 2 *
      q3ModelAmplitude M h (wholeRootShellLabel j N i) ^ 2) ≤ _
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (wholeRootBand_variance_clock j N hjN M h σ hσ
        (wholeRoot_frame_variance_lower M h j hstate) weights hweights)
  have hlength : 0 < wholeRootBandLength j N := by
    have hcast : ((wholeRootBandLength j N : ℕ) : ℤ) = N - j := by
      dsimp [wholeRootBandLength]
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hjN)
    have hcastpos : (0 : ℤ) < (wholeRootBandLength j N : ℤ) := by
      rw [hcast]
      omega
    exact_mod_cast hcastpos
  let instMissingWaveStatisticBandLengthNeZero :
      NeZero (wholeRootBandLength j N) := ⟨Nat.ne_of_gt hlength⟩
  have hab : a < a + R := by linarith
  have hcd : c < c + R := by linarith
  have hseries := @q3WeightedBandH3_missingWave_bound
    (wholeRootBandLength j N) instMissingWaveStatisticBandLengthNeZero
    a c R σ hR hσ hab hcd β w L
    (M.gamma * (N - j : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (N - j : ℝ))) p hA hvar hp
  have htransfer := @wholeRoot_actualBand_eLpNorm_eq
    (wholeRootBandLength j N) instMissingWaveStatisticBandLengthNeZero
    a (a + R) c (c + R) R σ hab hcd M h hM
    (wholeRootShellLabel j N) (wholeRootShellLabel_injective j N)
    (wholeRootWeights j N weights) (q := p)
  have hmodel :
      eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
          j N weights ω)) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (fun ω => wholeRootSpatialStatistic σ R
        (q3WeightedBandH3Value a (a + R) c (c + R) β w L
          (q3BandSeries a (a + R) c (c + R) β L ω)))
        (ENNReal.ofReal p) standardGaussianInfinitePi := by
    simpa only [wholeRootModelBand] using htransfer
  change (eLpNorm (fun ω => wholeRootSpatialStatistic σ R
      (wholeRootModelBand (a := a) (b := a + R) (c := c) (d := c + R)
        j N weights ω)) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure).toReal ≤ _
  rw [hmodel]
  simpa only [R, σ, β, w, L] using hseries


/-- The honest extended norm bound requires only a nonempty shell band;
there is no restriction on the observation square's scale. -/
theorem physical_missing_wave_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (j n N : ℤ) (hjN : j ≤ N)
    (hstate : nativeInductionState M h j) (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalMissingWave M j n N a c weights) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (40*(p+2)*(M.gamma*(N-j:ℝ)*(3:ℝ)^(2*M.gamma*(N-j:ℝ)))) := by
  rcases lt_or_eq_of_le hjN with hstrict | rfl
  · have hm := physical_missing_wave_memLp M h hM j n N hjN a c weights p hp
    rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal
      (missing_wave_toReal_le (n := n) hstrict M h hM hstate a c weights hw
        (by linarith only [hp]))
  · rw [physical_missing_wave_empty]
    norm_num

end
end ASDExplicitGamma.Inverse
