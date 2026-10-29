module

public import ASDExplicitGamma.Main.InverseLowerAlgebra
public import ASDExplicitGamma.Main.ObsLowerSourceRow
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Gaussian.Q3ModelCovariance

/-! At every observer `Q = originCube 2 (m + hobs)` with source depth `hobs + 5` and shell length
`3^(m+1)`, the physical column/row coefficients are the explicit MA coefficients
`k_a, k_b` at `v = (|σ⁻¹| |b|)^2`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse

theorem obs_mesh_ratio (m : ℤ) (hobs : ℕ) :
    diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) =
      (1 / 729 : ℝ) * (q3ModelLength (m + 1)).1 := by
  have hL : (q3ModelLength (m + 1)).1 = 3 * (3 : ℝ) ^ m := by
    change (3 : ℝ) ^ (m + 1) = _
    rw [zpow_add_one₀ (by norm_num)]
    ring
  have hr : diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5) = (3 : ℝ) ^ m / 243 := by
    unfold diagMeshRadius
    rw [cubeScaleFactor_originCube, zpow_add₀ (by norm_num), zpow_natCast, pow_add]
    field_simp
    norm_num
  rw [hr, hL]
  ring

theorem obs_colC_eq (m : ℤ) (hobs : ℕ) (b σ : ℝ) :
    |σ⁻¹| * obsColumnCoefficient (originCube 2 (m + hobs)) (hobs + 5) b
        (q3ModelLength (m + 1)) = mainInverseKA ((|σ⁻¹| * |b|) ^ 2) := by
  have hL0 : 0 < (q3ModelLength (m + 1)).1 := (q3ModelLength (m + 1)).2
  set L := (q3ModelLength (m + 1)).1 with hLdef
  have hr := obs_mesh_ratio m hobs
  unfold obsColumnCoefficient mainInverseKA mainInverseA2 mainInverseA4
  rw [hr]
  have e1 : Real.sqrt ((156 / 5 : ℝ) * b ^ 2 / L ^ 2) =
      Real.sqrt (156 / 5 : ℝ) * |b| / L := by
    rw [show (156 / 5 : ℝ) * b ^ 2 / L ^ 2 = (Real.sqrt (156 / 5 : ℝ) * |b| / L) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 156 / 5 by norm_num), sq_abs]; try ring]
    exact Real.sqrt_sq (by positivity)
  have e2 : Real.sqrt ((46488 / 25 : ℝ) * b ^ 2 / L ^ 4) =
      Real.sqrt (46488 / 25 : ℝ) * |b| / L ^ 2 := by
    rw [show (46488 / 25 : ℝ) * b ^ 2 / L ^ 4 = (Real.sqrt (46488 / 25 : ℝ) * |b| / L ^ 2) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 46488 / 25 by norm_num), sq_abs]; try ring]
    exact Real.sqrt_sq (by positivity)
  have e3 : Real.sqrt ((156 / 5 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 12)) =
      Real.sqrt (156 / 5 : ℝ) * (|σ⁻¹| * |b|) / 729 := by
    rw [show (156 / 5 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 12) =
      (Real.sqrt (156 / 5 : ℝ) * (|σ⁻¹| * |b|) / 729) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 156 / 5 by norm_num)]; try ring]
    exact Real.sqrt_sq (by positivity)
  have e4 : Real.sqrt ((46488 / 25 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 24)) =
      Real.sqrt (46488 / 25 : ℝ) * (|σ⁻¹| * |b|) / 729 ^ 2 := by
    rw [show (46488 / 25 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 24) =
      (Real.sqrt (46488 / 25 : ℝ) * (|σ⁻¹| * |b|) / 729 ^ 2) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 46488 / 25 by norm_num)]; try ring]
    exact Real.sqrt_sq (by positivity)
  rw [e1, e2, e3, e4, Real.sqrt_sq (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
    Real.sqrt_sq_eq_abs]
  field_simp
  ring

theorem obs_rowC_eq (m : ℤ) (hobs : ℕ) (b σ : ℝ) :
    |σ⁻¹| * mainQ3RowConstant
        (diagMeshRadius (originCube 2 (m + hobs)) (hobs + 5)) b
        (q3ModelLength (m + 1)).1 = mainInverseKB ((|σ⁻¹| * |b|) ^ 2) := by
  have hL0 : 0 < (q3ModelLength (m + 1)).1 := (q3ModelLength (m + 1)).2
  set L := (q3ModelLength (m + 1)).1 with hLdef
  have hr := obs_mesh_ratio m hobs
  unfold mainQ3RowConstant mainInverseKB mainInverseA2 mainInverseA4
  rw [hr]
  have e1 : Real.sqrt ((78 / 5 : ℝ) * b ^ 2 / L ^ 2) =
      Real.sqrt (78 / 5 : ℝ) * |b| / L := by
    rw [show (78 / 5 : ℝ) * b ^ 2 / L ^ 2 = (Real.sqrt (78 / 5 : ℝ) * |b| / L) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 78 / 5 by norm_num), sq_abs]; try ring]
    exact Real.sqrt_sq (by positivity)
  have e2 : Real.sqrt ((23244 / 25 : ℝ) * b ^ 2 / L ^ 4) =
      Real.sqrt (23244 / 25 : ℝ) * |b| / L ^ 2 := by
    rw [show (23244 / 25 : ℝ) * b ^ 2 / L ^ 4 = (Real.sqrt (23244 / 25 : ℝ) * |b| / L ^ 2) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 23244 / 25 by norm_num), sq_abs]; try ring]
    exact Real.sqrt_sq (by positivity)
  have e3 : Real.sqrt ((78 / 5 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 12)) =
      Real.sqrt (78 / 5 : ℝ) * (|σ⁻¹| * |b|) / 729 := by
    rw [show (78 / 5 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 12) =
      (Real.sqrt (78 / 5 : ℝ) * (|σ⁻¹| * |b|) / 729) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 78 / 5 by norm_num)]; try ring]
    exact Real.sqrt_sq (by positivity)
  have e4 : Real.sqrt ((23244 / 25 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 24)) =
      Real.sqrt (23244 / 25 : ℝ) * (|σ⁻¹| * |b|) / 729 ^ 2 := by
    rw [show (23244 / 25 : ℝ) * ((|σ⁻¹| * |b|) ^ 2 / 3 ^ 24) =
      (Real.sqrt (23244 / 25 : ℝ) * (|σ⁻¹| * |b|) / 729 ^ 2) ^ 2 by
      simp only [div_pow, mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 23244 / 25 by norm_num)]; try ring]
    exact Real.sqrt_sq (by positivity)
  rw [e1, e2, e3, e4, Real.sqrt_sq (mul_nonneg (abs_nonneg _) (abs_nonneg _)),
    Real.sqrt_sq_eq_abs]
  field_simp
  ring

end ASDExplicitGamma.Main
