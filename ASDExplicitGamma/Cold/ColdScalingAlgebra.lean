module

public import ASDExplicitGamma.Cold.ColdMomentRecursion
public import ASDExplicitGamma.Cold.ColdHistoryCaps

/-! # Proportional cold caps with frozen thresholds -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The exact centered moment cap is homogeneous in the input cap. -/
theorem coldCenteredMomentCap_scale {θ : ℝ} (hθ : 0 ≤ θ) (M : ℝ) (d : ℕ) :
    coldCenteredMomentCap (θ*M) d = θ*coldCenteredMomentCap M d := by
  unfold coldCenteredMomentCap
  split_ifs
  · rfl
  · rw [mul_min_of_nonneg _ _ hθ]
    congr 1
    ring

/-- Nonnegative scalar multiplication commutes with an attained finite minimum. -/
theorem cold_inf_scale {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    s.inf' hs (fun i => θ*f i) = θ*s.inf' hs f := by
  apply le_antisymm
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' (α := OrderDual ℝ) hs f
    change s.inf' hs f = f i at he
    rw [he]
    exact Finset.inf'_le _ hi
  · apply Finset.le_inf' hs
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hi) hθ

/-- Every source depth cap scales exactly, including all transported candidates. -/
theorem coldHistoryDepthCap_scale {θ : ℝ} (hθ : 0 ≤ θ) (M D : ℕ → ℝ) (j r : ℕ) :
    coldHistoryDepthCap (fun k => θ*M k) (fun k => θ*D k) j r = θ*coldHistoryDepthCap M D j r := by
  unfold coldHistoryDepthCap
  simp_rw [coldCenteredMomentCap_scale hθ]
  have he (k : ℕ) : θ*D k+(9:ℝ)^((r:ℝ)/20)*(θ*coldCenteredMomentCap (M k) (j-r-k)) =
      θ*(D k+(9:ℝ)^((r:ℝ)/20)*coldCenteredMomentCap (M k) (j-r-k)) := by ring
  simp_rw [he,cold_inf_scale _ _ _ hθ]
  rw [mul_min_of_nonneg _ _ hθ]
  congr 1
  ring

/-- The old-history branch, including its complete fine tail, scales exactly. -/
theorem coldOldHistoryCap_scale (θ a R S : ℝ) (j : ℕ) :
    coldOldHistoryCap (θ*a) (θ*R) (θ*S) j = θ*coldOldHistoryCap a R S j := by
  unfold coldOldHistoryCap
  ring

/-- All three complete-history candidates scale exactly before outward rounding. -/
theorem coldTriangularHistoryCap_scale {θ : ℝ} (hθ : 0 ≤ θ)
    (M D : ℕ → ℝ) (a R S : ℝ) (j : ℕ) :
    coldTriangularHistoryCap (fun k => θ*M k) (fun k => θ*D k) (θ*a) (θ*R) (θ*S) j =
      θ*coldTriangularHistoryCap M D a R S j := by
  unfold coldTriangularHistoryCap
  simp_rw [coldOldHistoryCap_scale,coldHistoryDepthCap_scale hθ]
  have he : (∑ r ∈ Finset.range j, coldHistoryAlpha^r*(θ*coldHistoryDepthCap M D j r)) =
      θ*(∑ r ∈ Finset.range j, coldHistoryAlpha^r*coldHistoryDepthCap M D j r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he,mul_min_of_nonneg _ _ hθ,mul_min_of_nonneg _ _ hθ]
  congr 2
  ring

/-- Under proportional means and L2 caps, the spectral variance radical scales
by at most sqrt(theta); this is the nonlinear input to all graph candidates. -/
theorem cold_spectral_radical_scale {θ D L : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Real.sqrt (2*(θ*D)+(θ*L)^2) ≤ Real.sqrt θ*Real.sqrt (2*D+L^2) := by
  rw [← Real.sqrt_mul hθ]
  apply Real.sqrt_le_sqrt
  have ht : θ^2 ≤ θ := by nlinarith only [hθ,hθ1]
  have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg L)
  nlinarith only [hm]

/-- A homogeneous quadratic graph radicand gains the full theta factor. -/
theorem cold_quadratic_radical_scale {θ a b : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) :
    Real.sqrt (θ^2*a+θ*b) ≤ Real.sqrt θ*Real.sqrt (a+b) := by
  rw [← Real.sqrt_mul hθ]
  apply Real.sqrt_le_sqrt
  have ht : θ^2 ≤ θ := by nlinarith only [hθ,hθ1]
  have hm := mul_le_mul_of_nonneg_right ht ha
  nlinarith only [hm]

/-- Squaring a sqrt(theta)-scaled graph norm pays theta, exactly. -/
theorem cold_graph_square_scale {θ x y : ℝ} (hθ : 0 ≤ θ) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hxy : x ≤ Real.sqrt θ*y) :
    2*x^2 ≤ θ*(2*y^2) := by
  have he := (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) hy)).mpr hxy
  rw [mul_pow,Real.sq_sqrt hθ] at he
  nlinarith only [he]

/-- For theta in [0,1], the twentieth-power charge is paid by theta. -/
theorem cold_bad_charge_le_scale {θ B : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hB : 0 ≤ B) : θ^20*B ≤ θ*B := by
  apply mul_le_mul_of_nonneg_right _ hB
  have hp : θ^19 ≤ 1 := pow_le_one₀ hθ hθ1
  calc
    θ^20 = θ^19*θ := pow_succ _ _
    _ ≤ 1*θ := mul_le_mul_of_nonneg_right hp hθ
    _ = θ := one_mul _

end ASDExplicitGamma.Cold
