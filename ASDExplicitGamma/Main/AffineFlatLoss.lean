module

public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Native.OldSignedAffineMeanLossCap
public import ASDExplicitGamma.Native.ParentBoundaryModelScales

/-! The depth-five flat mean-loss allowance in MA-AFFINE has exactly the
source `A₂` scale for the actual `m+1` q3 shell. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic Algsuperdiff.Section3

noncomputable section

/-- The flat mean-loss allowance is unchanged when the observer cube is
enlarged by `hobs` levels and the source partition depth is increased by the
same amount. The remaining six-level ratio is exactly the one in `A₂`. -/
theorem main_affine_flat_mean_loss_pair_cap_observer
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (hobs : ℕ) :
    let Q : TriadicCube 2 := originCube 2 (m + (hobs : ℤ))
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    oldSignedFlatMeanLoss Q (hobs + 5) b L true +
        oldSignedFlatMeanLoss Q (hobs + 5) b L false ≤
      (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9 := by
  dsimp only
  let Q : TriadicCube 2 := originCube 2 (m + (hobs : ℤ))
  let b : ℝ := q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)
  let L := q3ModelLength (m + 1)
  have hratio : cubeScaleFactor Q / L.1 =
      (3 : ℝ) ^ ((hobs : ℤ) - 1) := by
    change cubeScaleFactor (originCube 2 (m + (hobs : ℤ))) /
      (3 : ℝ) ^ (m + 1) = _
    rw [cubeScaleFactor_originCube]
    rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    omega
  have hscale : cubeScaleFactor Q / (3 : ℝ) ^ (hobs + 5) / L.1 =
      (3 : ℝ) ^ (-6 : ℤ) := by
    have hnat : (3 : ℝ) ^ (hobs + 5) =
        (3 : ℝ) ^ ((hobs + 5 : ℕ) : ℤ) := by
      rw [zpow_natCast]
    calc
      _ = (cubeScaleFactor Q / L.1) / (3 : ℝ) ^ (hobs + 5) := by
        field_simp [L.2.ne']
      _ = (3 : ℝ) ^ ((hobs : ℤ) - 1) /
          (3 : ℝ) ^ ((hobs + 5 : ℕ) : ℤ) := by rw [hratio, hnat]
      _ = (3 : ℝ) ^ (((hobs : ℤ) - 1) - ((hobs + 5 : ℕ) : ℤ)) := by
        rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
      _ = (3 : ℝ) ^ (-6 : ℤ) := by
        congr 1
        omega
  have hfactor :
      (cubeScaleFactor Q / (3 : ℝ) ^ (hobs + 5)) ^ 2 * b ^ 2 / L.1 ^ 2 =
        (cubeScaleFactor Q / (3 : ℝ) ^ (hobs + 5) / L.1) ^ 2 * b ^ 2 := by
    field_simp [L.2.ne']
  have hpow : ((3 : ℝ) ^ (-6 : ℤ)) ^ 2 = (3 : ℝ) ^ (-12 : ℤ) := by
    norm_num [zpow_neg]
  have hA2 :
      (cubeScaleFactor Q / (3 : ℝ) ^ (hobs + 5)) ^ 2 * b ^ 2 / L.1 ^ 2 =
        mainA2 (b ^ 2) := by
    rw [hfactor, hscale, hpow]
    simp [mainA2]
    ring
  calc
    _ ≤ (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) *
        ((cubeScaleFactor Q / (3 : ℝ) ^ (hobs + 5)) ^ 2 * b ^ 2 / L.1 ^ 2) / 9 := by
          simpa [Q, b, L] using old_signed_flat_mean_loss_pair_cap Q (hobs + 5) b L
    _ = (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9 := by
          rw [hA2]

end
end ASDExplicitGamma.Main
