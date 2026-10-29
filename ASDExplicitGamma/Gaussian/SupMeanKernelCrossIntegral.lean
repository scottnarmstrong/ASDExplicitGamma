module

public import ASDExplicitGamma.Gaussian.SupMeanKernelParity

/-! Exact cross-section integrals and parity cancellation for the actual white-noise factor. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model MeasureTheory
open scoped RealInnerProductSpace
noncomputable section

/-- Tensor products retain the exact planar Lebesgue normalization. -/
theorem supMean_integral_coordinate_product (f g : ℝ → ℝ) :
    (∫ y : Vec 2, f (y 0)*g (y 1)) = (∫ s, f s)*(∫ t, g t) := by
  calc
    _ = ∫ p : ℝ × ℝ, f p.1*g p.2 ∂volume.prod volume :=
      (volume_preserving_finTwoArrow ℝ).integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding _
    _ = _ := integral_prod_mul f g

/-- The exact one-dimensional Jacobian also applies to mixed derivative orders. -/
theorem supMean_integral_scaled_kernel_cross (L : {l : ℝ // 0 < l}) (r s : Fin 4) (x : ℝ) :
    (∫ y : ℝ, q3Derivative r ((x-y)/L.val)*q3Derivative s ((x-y)/L.val)) =
      L.val*(∫ z : ℝ, q3Derivative r z*q3Derivative s z) := by
  calc
    _ = ∫ z : ℝ, q3Derivative r (z/L.val)*q3Derivative s (z/L.val) := by
      simpa only [] using! integral_sub_left_eq_self
        (fun z : ℝ => q3Derivative r (z/L.val)*q3Derivative s (z/L.val)) volume x
    _ = _ := by
      simpa only [abs_of_pos L.property, smul_eq_mul] using!
        Measure.integral_comp_div (fun z : ℝ => q3Derivative r z*q3Derivative s z) L.val

/-- Mixed Hilbert kernel Gram rows at a point are literal products of ordinary
one-dimensional cross integrals. -/
theorem supMean_kernel_same_point_cross (β : ℝ) (L : {l : ℝ // 0 < l})
    (a b : H3Index) (x : Vec 2) :
    ⟪q3Section β L a x,q3Section β L b x⟫ =
      (β/L.val^(1+a.val.1.val+a.val.2.val)) * (β/L.val^(1+b.val.1.val+b.val.2.val)) *
        (L.val*(∫ t : ℝ, q3Derivative a.val.1 t*q3Derivative b.val.1 t)) *
        (L.val*(∫ t : ℝ, q3Derivative a.val.2 t*q3Derivative b.val.2 t)) := by
  rw [L2.inner_def]
  have he : (fun y : Vec 2 => inner ℝ (q3Section β L a x y) (q3Section β L b x y)) =ᵐ[volume]
      (fun y => ((β/L.val^(1+a.val.1.val+a.val.2.val))*(β/L.val^(1+b.val.1.val+b.val.2.val))) *
        ((q3Derivative a.val.1 ((x 0-y 0)/L.val)*q3Derivative b.val.1 ((x 0-y 0)/L.val)) *
         (q3Derivative a.val.2 ((x 1-y 1)/L.val)*q3Derivative b.val.2 ((x 1-y 1)/L.val)))) := by
    filter_upwards [(q3SectionFunction_memLp β L a x).coeFn_toLp,
      (q3SectionFunction_memLp β L b x).coeFn_toLp] with y ha hb
    change q3Section β L a x y = _ at ha
    change q3Section β L b x y = _ at hb
    rw [ha,hb]
    simp only [q3SectionFunction, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  have ht := supMean_integral_coordinate_product
    (fun z => q3Derivative a.val.1 ((x 0-z)/L.val)*q3Derivative b.val.1 ((x 0-z)/L.val))
    (fun z => q3Derivative a.val.2 ((x 1-z)/L.val)*q3Derivative b.val.2 ((x 1-z)/L.val))
  rw [integral_congr_ae he, integral_const_mul]
  calc
    _ = ((β/L.val^(1+a.val.1.val+a.val.2.val))*(β/L.val^(1+b.val.1.val+b.val.2.val))) *
        ((∫ z : ℝ, q3Derivative a.val.1 ((x 0-z)/L.val)*q3Derivative b.val.1 ((x 0-z)/L.val)) *
         (∫ z : ℝ, q3Derivative a.val.2 ((x 1-z)/L.val)*q3Derivative b.val.2 ((x 1-z)/L.val))) :=
      congrArg (fun z : ℝ => ((β/L.val^(1+a.val.1.val+a.val.2.val))*
        (β/L.val^(1+b.val.1.val+b.val.2.val)))*z) ht
    _ = _ := by
      rw [supMean_integral_scaled_kernel_cross, supMean_integral_scaled_kernel_cross]
      ring

/-- Odd first-coordinate cross order forces actual Hilbert orthogonality. -/
theorem supMean_kernel_cross_orthogonal (β : ℝ) (L : {l : ℝ // 0 < l})
    (a b : H3Index) (x : Vec 2) (hodd : Odd (a.val.1.val+b.val.1.val)) :
    ⟪q3Section β L a x,q3Section β L b x⟫ = 0 := by
  rw [supMean_kernel_same_point_cross, supMean_kernel_cross_integral_zero _ _ hodd]
  ring

end
end ASDExplicitGamma.Gaussian
