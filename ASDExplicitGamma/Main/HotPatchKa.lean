module

public import ASDExplicitGamma.Main.HotPatchSourceBound
public import ASDExplicitGamma.Main.ErrorCoefficients
public import ASDExplicitGamma.Gaussian.Q3ModelCovariance

/-! Hot-patch trial: the DIAG source multiplier at the actual conventions
`Q = originCube 2 m`, depth five, `L = 3^(m+1)` is exactly the main coefficient
`k_a`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Native ASDExplicitGamma.Triadic
open ASDExplicitGamma.Gaussian

/-- The depth-five cells of the root have side `3^(m-5)`, the shell length is `3^(m+1)`,
so `r / L = 3^(-6)` and the source multiplier is the held `k_a`. -/
theorem hot_source_multiplier_eq_mainKa (m : ℤ) (hobs : ℕ) (b : ℝ) :
    oldSignedSourceMultiplier (originCube 2 (m + hobs)) (hobs + 5) b
        (q3ModelLength (m + 1)) = mainKa (b ^ 2) := by
  have hu : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have hL : (q3ModelLength (m + 1)).1 = 3 * (3 : ℝ) ^ m := by
    change (3 : ℝ) ^ (m + 1) = _
    rw [zpow_add_one₀ (by norm_num)]
    ring
  have hr : diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) = (3 : ℝ) ^ m / 243 := by
    unfold diagMeshRadius
    rw [cubeScaleFactor_originCube, zpow_add₀ (by norm_num), zpow_natCast, pow_add]
    field_simp
    norm_num
  have hratio : diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) / (q3ModelLength (m + 1)).1 = 1 / 729 := by
    rw [hr, hL]
    field_simp
    norm_num
  have hA2 : mainA2 (b ^ 2) = b ^ 2 * (1 / 729) ^ 2 := by
    unfold mainA2
    norm_num [zpow_neg]
  have hA4 : mainA4 (b ^ 2) = b ^ 2 * (1 / 729) ^ 4 := by
    unfold mainA4
    norm_num [zpow_neg]
  have hLr : (q3ModelLength (m + 1)).1 = diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) * 729 := by
    rw [hL, hr]
    ring
  have hL0 : 0 < (q3ModelLength (m + 1)).1 := (q3ModelLength (m + 1)).2
  have hr0 : 0 < diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) := diagMeshRadius_pos _ _
  have e2 : diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) *
      Real.sqrt ((156 / 5) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 2) =
      Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) := by
    rw [hA2]
    have : (156 / 5) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 2 *
        diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) ^ 2 = (156 / 5) * (b ^ 2 * (1 / 729) ^ 2) := by
      rw [hLr]
      field_simp
    rw [← this, Real.sqrt_mul (by positivity), Real.sqrt_sq hr0.le, mul_comm]
  have e4 : diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) ^ 2 *
      Real.sqrt ((46488 / 25) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 4) =
      Real.sqrt ((46488 / 25) * mainA4 (b ^ 2)) := by
    rw [hA4]
    have : (46488 / 25) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 4 *
        (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) ^ 2) ^ 2 =
        (46488 / 25) * (b ^ 2 * (1 / 729) ^ 4) := by
      rw [hLr]
      field_simp
    rw [← this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_comm]
  unfold oldSignedSourceMultiplier mainKa
  calc Real.sqrt (b ^ 2) + diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) * (36 / 25) *
        Real.sqrt ((156 / 5) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 2) +
      diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) ^ 2 * (57 / 200) *
        Real.sqrt ((46488 / 25) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 4)
      = Real.sqrt (b ^ 2) + (36 / 25) * (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) *
        Real.sqrt ((156 / 5) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 2)) +
      (57 / 200) * (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) ^ 2 *
        Real.sqrt ((46488 / 25) * b ^ 2 / (q3ModelLength (m + 1)).1 ^ 4)) := by ring
    _ = _ := by rw [e2, e4]; norm_num

end ASDExplicitGamma.Main
