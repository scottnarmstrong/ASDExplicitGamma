module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Deterministic weighted square estimates for the Hilbert Gaussian envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- Weighted Young's inequality in the exact square form needed by the envelope. -/
theorem chaos_weighted_square (s u v : ℝ) (hs : 0 < s) :
    (u+v)^2 ≤ (1+s)*u^2+(1+s⁻¹)*v^2 := by
  have he : s*((1+s)*u^2+(1+s⁻¹)*v^2-(u+v)^2) = (s*u-v)^2 := by
    field_simp
    ring
  have hh : 0 ≤ s*((1+s)*u^2+(1+s⁻¹)*v^2-(u+v)^2) := by rw [he]; exact sq_nonneg _
  have hd := nonneg_of_mul_nonneg_right hh hs
  linarith only [hd]

/-- Weighted Young summed over orthonormal coordinates. -/
theorem chaos_weighted_norm_square {d : ℕ} (s : ℝ) (hs : 0 < s) (m c : Fin d → ℝ) :
    (∑ i, (m i+c i)^2) ≤ (1+s)*(∑ i, (m i)^2)+(1+s⁻¹)*(∑ i, (c i)^2) := by
  calc
    _ ≤ ∑ i, ((1+s)*(m i)^2+(1+s⁻¹)*(c i)^2) :=
      Finset.sum_le_sum (fun i _ => chaos_weighted_square s (m i) (c i) hs)
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]

theorem chaos_envelope_constants :
    0 < 1+Real.sqrt 15 ∧ 0 ≤ 1+(Real.sqrt 15)⁻¹ ∧
    1+(Real.sqrt 15)⁻¹ ≤ 1+Real.sqrt 15 ∧
    15*(1+(Real.sqrt 15)⁻¹)^2 = (1+Real.sqrt 15)^2 := by
  have hs : (0:ℝ) < Real.sqrt 15 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : (1:ℝ) ≤ Real.sqrt 15 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hd : 1+(Real.sqrt 15)⁻¹ = (1+Real.sqrt 15)/Real.sqrt 15 := by
    field_simp
    ring
  refine ⟨by positivity,by positivity,?_,?_⟩
  · linarith only [(inv_le_one_of_one_le₀ hs1).trans hs1]
  · rw [hd,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)]
    ring

/-- The integrated polynomial majorant closes with the exact source constant. -/
theorem chaos_shift_moment_algebra (C D a b V : ℝ) (hC : 0 ≤ C) (hD : D ≤ C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hV : V ≤ 15*b^2) (hCD : 15*D^2 = C^2) :
    C^2*a^2+2*C*a*D*b+D^2*V ≤ C^2*(a+b)^2 := by
  have hv : D^2*V ≤ C^2*b^2 := by
    calc
      _ ≤ D^2*(15*b^2) := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
      _ = (15*D^2)*b^2 := by ring
      _ = _ := by rw [hCD]
  have hh := mul_le_mul_of_nonneg_left hD (by positivity : (0:ℝ) ≤ 2*C*a*b)
  nlinarith only [hv,hh]

end ASDExplicitGamma.Scalar
