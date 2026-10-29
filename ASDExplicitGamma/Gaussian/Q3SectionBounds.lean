module

public import ASDExplicitGamma.Gaussian.H3KernelSections
public import ASDExplicitGamma.Gaussian.Q3KernelLipschitz

/-! # Uniform spatial bounds and support of the physical q3 derivative sections -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology NNReal RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

private theorem product_lipschitz {E : Type*} [SeminormedAddCommGroup E]
    (f g : E → ℝ) (A B : ℝ≥0) (Cf Cg : ℝ≥0)
    (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g)
    (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖g x‖ ≤ B) :
    LipschitzWith (A * Cg + B * Cf) (fun x => f x * g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖f x * g x - f y * g y‖ = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by congr 1; ring
    _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      simpa only [norm_mul] using norm_add_le (f x * (g x - g y)) ((f x - f y) * g y)
    _ ≤ (A : ℝ) * ((Cg : ℝ) * ‖x - y‖) + ((Cf : ℝ) * ‖x - y‖) * (B : ℝ) :=
      add_le_add
        (mul_le_mul (hA x) (hg.norm_sub_le x y) (norm_nonneg _) A.2)
        (mul_le_mul (hf.norm_sub_le x y) (hB y) (norm_nonneg _) (mul_nonneg Cf.2 (norm_nonneg _)))
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

/-- For every derivative coordinate through order two there is one global spatial Lipschitz
constant, independent of the white-noise variable. -/
theorem q3SectionFunction_lipschitz (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) :
    ∃ C : ℝ≥0, ∀ y, LipschitzWith C (fun x => q3SectionFunction b L a x y) := by
  obtain ⟨C₁, hC₁⟩ := q3Derivative_lipschitz a.1.1 (by omega)
  obtain ⟨C₂, hC₂⟩ := q3Derivative_lipschitz a.1.2 (by omega)
  obtain ⟨B₁, hB₁, hb₁⟩ := q3Derivative_bounded a.1.1
  obtain ⟨B₂, hB₂, hb₂⟩ := q3Derivative_bounded a.1.2
  let A : ℝ≥0 := ⟨B₁, hB₁⟩
  let B : ℝ≥0 := ⟨B₂, hB₂⟩
  let c : ℝ≥0 := Real.nnabs (b / L.1 ^ (1 + a.1.1.val + a.1.2.val))
  let d : ℝ≥0 := Real.nnabs L.1⁻¹
  refine ⟨c * (A * (C₂ * d) + B * (C₁ * d)), fun y => ?_⟩
  have hd (i : Fin 2) : LipschitzWith d (fun x : Vec 2 => (x i - y i) / L.1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    rw [dist_eq_norm, dist_eq_norm]
    have he : (x i - y i) / L.1 - (z i - y i) / L.1 = (x i - z i) * L.1⁻¹ := by ring
    rw [he, norm_mul]
    change _ ≤ |L.1⁻¹| * ‖x - z‖
    calc
      _ ≤ ‖x - z‖ * |L.1⁻¹| := mul_le_mul_of_nonneg_right (norm_le_pi_norm (x - z) i) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hp := product_lipschitz
    (fun x : Vec 2 => q3Derivative a.1.1 ((x 0 - y 0) / L.1))
    (fun x : Vec 2 => q3Derivative a.1.2 ((x 1 - y 1) / L.1)) A B
    (C₁ * d) (C₂ * d) (hC₁.comp (hd 0)) (hC₂.comp (hd 1)) (fun _ => hb₁ _) (fun _ => hb₂ _)
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [dist_eq_norm, dist_eq_norm]
  unfold q3SectionFunction
  rw [← mul_sub, norm_mul]
  calc
    _ ≤ ‖b / L.1 ^ (1 + a.1.1.val + a.1.2.val)‖ *
        ((A * (C₂ * d) + B * (C₁ * d) : ℝ≥0) * ‖x - z‖) :=
      mul_le_mul_of_nonneg_left (hp.norm_sub_le x z) (norm_nonneg _)
    _ = _ := by simp only [NNReal.coe_mul, c, Real.coe_nnabs, Real.norm_eq_abs]; ring

/-- Nearby spatial points use white-noise inputs in one fixed compact ball. -/
theorem q3SectionFunction_local_support (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (x : Vec 2) {z y : Vec 2} (hz : z ∈ Metric.ball x 1)
    (hy : y ∉ Metric.closedBall x (1 + L.1)) : q3SectionFunction b L a z y = 0 := by
  have hnot : ¬ ∀ i : Fin 2, |(z i - y i) / L.1| ≤ 1 / 2 := by
    intro hh
    apply hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (by linarith [L.2] : 0 ≤ 1 + L.1)).mpr
    intro i
    have hi := hh i
    rw [abs_div, abs_of_pos L.2] at hi
    have hiy : |z i - y i| ≤ L.1 / 2 := by
      have := (div_le_iff₀ L.2).mp hi
      linarith
    have hiz : |z i - x i| < 1 :=
      (norm_le_pi_norm (z - x) i).trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using hz)
    change |y i - x i| ≤ 1 + L.1
    have ht : |y i - x i| ≤ |z i - y i| + |z i - x i| := by
      have he : y i - x i = -(z i - y i) + (z i - x i) := by ring
      rw [he]
      simpa only [abs_neg] using abs_add_le (-(z i - y i)) (z i - x i)
    linarith [L.2]
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hi' := q3Derivative_eq_zero (lt_of_not_ge hi)
  fin_cases i
  · have hh : q3Derivative a.1.1 ((z 0 - y 0) / L.1) = 0 := hi' a.1.1
    simp only [q3SectionFunction, hh, zero_mul, mul_zero]
  · have hh : q3Derivative a.1.2 ((z 1 - y 1) / L.1) = 0 := hi' a.1.2
    simp only [q3SectionFunction, hh, mul_zero]

end ASDExplicitGamma.Gaussian
