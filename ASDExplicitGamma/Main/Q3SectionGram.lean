module

public import ASDExplicitGamma.Main.Q3KernelGram

/-! Exact same-point tensor Gram entries for the physical q3 covariance factor. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open MeasureTheory Homogenization ASDExplicitGamma.Gaussian
open scoped RealInnerProductSpace

/-- The common scale and reflection preserve signed cross moments. -/
theorem main_q3_scaled_kernel_gram (L : {l : ℝ // 0 < l}) (r s : Fin 3) (x : ℝ) :
    (∫ y, q3Derivative ⟨r.val, by omega⟩ ((x-y)/L.1)*
      q3Derivative ⟨s.val, by omega⟩ ((x-y)/L.1)) = L.1*mainQ3KernelGram r s := by
  rw [integral_sub_left_eq_self (fun z => q3Derivative ⟨r.val, by omega⟩ (z/L.1)*
    q3Derivative ⟨s.val, by omega⟩ (z/L.1)) volume x,
    Measure.integral_comp_div (fun z => q3Derivative ⟨r.val, by omega⟩ z*
      q3Derivative ⟨s.val, by omega⟩ z) L.1,
    abs_of_pos L.2, smul_eq_mul, main_q3_kernel_gram]

/-- Full same-point jet Gram matrix in tensor form. The normalization retains
both the white-noise Jacobian and the derivative powers of the physical length. -/
theorem main_q3_section_gram (b : ℝ) (L : {l : ℝ // 0 < l}) (a c : H3Index)
    (ha0 : a.1.1.val < 3) (ha1 : a.1.2.val < 3)
    (hc0 : c.1.1.val < 3) (hc1 : c.1.2.val < 3) (x : Vec 2) :
    ⟪q3Section b L a x, q3Section b L c x⟫ =
      (b/L.1^(1+a.1.1.val+a.1.2.val))*(b/L.1^(1+c.1.1.val+c.1.2.val))*
        (L.1*mainQ3KernelGram ⟨a.1.1.val, ha0⟩ ⟨c.1.1.val, hc0⟩)*
        (L.1*mainQ3KernelGram ⟨a.1.2.val, ha1⟩ ⟨c.1.2.val, hc1⟩) := by
  rw [L2.inner_def]
  have he : (∫ w, inner ℝ (q3Section b L a x w) (q3Section b L c x w)) =
      (b/L.1^(1+a.1.1.val+a.1.2.val))*(b/L.1^(1+c.1.1.val+c.1.2.val))*
      ∫ w : Vec 2,
        (q3Derivative a.1.1 ((x 0-w 0)/L.1)*q3Derivative c.1.1 ((x 0-w 0)/L.1))*
        (q3Derivative a.1.2 ((x 1-w 1)/L.1)*q3Derivative c.1.2 ((x 1-w 1)/L.1)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(q3SectionFunction_memLp b L a x).coeFn_toLp,
      (q3SectionFunction_memLp b L c x).coeFn_toLp] with w hw hw'
    change q3Section b L a x w = _ at hw
    change q3Section b L c x w = _ at hw'
    rw [hw, hw']
    simp only [q3SectionFunction, RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [he]
  have ht := (volume_preserving_finTwoArrow ℝ).integral_comp
    MeasurableEquiv.finTwoArrow.measurableEmbedding
    (fun p : ℝ × ℝ =>
      (q3Derivative a.1.1 ((x 0-p.1)/L.1)*q3Derivative c.1.1 ((x 0-p.1)/L.1))*
      (q3Derivative a.1.2 ((x 1-p.2)/L.1)*q3Derivative c.1.2 ((x 1-p.2)/L.1)))
  change (∫ w : Vec 2,
      (q3Derivative a.1.1 ((x 0-w 0)/L.1)*q3Derivative c.1.1 ((x 0-w 0)/L.1))*
      (q3Derivative a.1.2 ((x 1-w 1)/L.1)*q3Derivative c.1.2 ((x 1-w 1)/L.1))) = _ at ht
  rw [ht, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
    integral_prod_mul
      (fun y => q3Derivative a.1.1 ((x 0-y)/L.1)*q3Derivative c.1.1 ((x 0-y)/L.1))
      (fun y => q3Derivative a.1.2 ((x 1-y)/L.1)*q3Derivative c.1.2 ((x 1-y)/L.1))]
  have h0 := main_q3_scaled_kernel_gram L ⟨a.1.1.val,ha0⟩ ⟨c.1.1.val,hc0⟩ (x 0)
  have h1 := main_q3_scaled_kernel_gram L ⟨a.1.2.val,ha1⟩ ⟨c.1.2.val,hc1⟩ (x 1)
  change (∫ y, q3Derivative a.1.1 ((x 0-y)/L.1)*q3Derivative c.1.1 ((x 0-y)/L.1)) = _ at h0
  change (∫ y, q3Derivative a.1.2 ((x 1-y)/L.1)*q3Derivative c.1.2 ((x 1-y)/L.1)) = _ at h1
  rw [h0, h1]
  ring

end ASDExplicitGamma.Main
