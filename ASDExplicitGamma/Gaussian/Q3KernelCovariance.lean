module

public import ASDExplicitGamma.Gaussian.H3KernelSections

/-! # The actual white-noise convolution factor has the frozen q3 covariance -/

@[expose] public section

open MeasureTheory Homogenization Set ASDExplicitGamma.Model
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

theorem integral_q3_scaled_cross (L : {l : ℝ // 0 < l}) (x z : ℝ) :
    (∫ y, q3Kernel ((x - y) / L.1) * q3Kernel ((z - y) / L.1)) =
      L.1 * q3Cov ((x - z) / L.1) := by
  have he : (fun y => q3Kernel ((x - y) / L.1) * q3Kernel ((z - y) / L.1)) =
      fun y => (fun w => q3Kernel (w / L.1) * q3Kernel (w / L.1 + (z - x) / L.1)) (x - y) := by
    funext y
    congr 2
    ring
  rw [he, integral_sub_left_eq_self (fun w => q3Kernel (w / L.1) * q3Kernel (w / L.1 + (z - x) / L.1)) volume x]
  have he' : (fun w => q3Kernel (w / L.1) * q3Kernel (w / L.1 + (z - x) / L.1)) =
      fun w => (fun r => q3Kernel r * q3Kernel (r + (z - x) / L.1)) (w / L.1) := rfl
  rw [he', Measure.integral_comp_div (fun r => q3Kernel r * q3Kernel (r + (z - x) / L.1)) L.1, abs_of_pos L.2, smul_eq_mul, ← q3Cov]
  rw [show (z - x) / L.1 = -((x - z) / L.1) by ring, q3Cov_even]

/-- The white-noise Jacobian cancels exactly the dimension-two L⁻² normalization. -/
theorem q3Section_covariance (b : ℝ) (L : {l : ℝ // 0 < l}) (x z : Vec 2) :
    ⟪q3Section b L h3Zero x, q3Section b L h3Zero z⟫ =
      b ^ 2 * q3Cov ((x 0 - z 0) / L.1) * q3Cov ((x 1 - z 1) / L.1) := by
  rw [L2.inner_def]
  have hrep (y : Vec 2) : q3SectionFunction b L h3Zero y =
      fun w => (b / L.1) * (q3Kernel ((y 0 - w 0) / L.1) * q3Kernel ((y 1 - w 1) / L.1)) := by
    funext w
    simp [q3SectionFunction, h3Zero, q3Derivative]
  have he : (∫ w, inner ℝ (q3Section b L h3Zero x w) (q3Section b L h3Zero z w)) =
      (b / L.1) ^ 2 * ∫ w : Vec 2,
        (q3Kernel ((x 0 - w 0) / L.1) * q3Kernel ((z 0 - w 0) / L.1)) *
          (q3Kernel ((x 1 - w 1) / L.1) * q3Kernel ((z 1 - w 1) / L.1)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(q3SectionFunction_memLp b L h3Zero x).coeFn_toLp,
      (q3SectionFunction_memLp b L h3Zero z).coeFn_toLp] with w hx hz
    change q3Section b L h3Zero x w = _ at hx
    change q3Section b L h3Zero z w = _ at hz
    rw [hx, hz, hrep x, hrep z]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [he]
  have ht := (volume_preserving_finTwoArrow ℝ).integral_comp
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : ℝ × ℝ =>
      (q3Kernel ((x 0 - p.1) / L.1) * q3Kernel ((z 0 - p.1) / L.1)) *
        (q3Kernel ((x 1 - p.2) / L.1) * q3Kernel ((z 1 - p.2) / L.1)))
  change (∫ w : Vec 2,
      (q3Kernel ((x 0 - w 0) / L.1) * q3Kernel ((z 0 - w 0) / L.1)) *
        (q3Kernel ((x 1 - w 1) / L.1) * q3Kernel ((z 1 - w 1) / L.1))) = _ at ht
  rw [ht, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
    integral_prod_mul (fun s => q3Kernel ((x 0 - s) / L.1) * q3Kernel ((z 0 - s) / L.1))
      (fun t => q3Kernel ((x 1 - t) / L.1) * q3Kernel ((z 1 - t) / L.1)),
    integral_q3_scaled_cross, integral_q3_scaled_cross]
  field_simp [L.2.ne']

end ASDExplicitGamma.Gaussian
