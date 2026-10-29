module

public import ASDExplicitGamma.Gaussian.H3KernelRegularity
public import ASDExplicitGamma.Gaussian.H3Space
public import ASDExplicitGamma.Gaussian.HilbertKernel
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # The scaled L² sections of the q3 convolution covariance factor -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The white-noise factor is the ordinary real L² space on the plane. -/
noncomputable abbrev WhiteNoise := Lp ℝ 2 (volume : Measure (Vec 2))

/-- Tensor products of scalar L² functions are in planar L². -/
theorem memLp_tensor {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume) :
    MemLp (fun y : Vec 2 => f (y 0) * g (y 1)) 2 volume := by
  have hprod : MemLp (fun p : ℝ × ℝ => f p.1 * g p.2) 2 (volume.prod volume) := by
    apply (memLp_two_iff_integrable_sq ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable).mpr
    simpa only [Pi.mul_apply, Function.comp_apply, mul_pow] using hf2.integrable_sq.mul_prod hg2.integrable_sq
  have hm : MemLp (fun p : ℝ × ℝ => f p.1 * g p.2) 2
      ((volume : Measure (Vec 2)).map MeasurableEquiv.finTwoArrow) := by
    rw [(volume_preserving_finTwoArrow ℝ).map_eq]
    exact hprod
  exact hm.comp_of_map MeasurableEquiv.finTwoArrow.measurable.aemeasurable

/-- The tensor integral has the product normalization, including both spatial coordinates. -/
theorem integral_tensor_sq (f g : ℝ → ℝ) :
    (∫ y : Vec 2, (f (y 0) * g (y 1)) ^ 2) =
      (∫ s, f s ^ 2) * ∫ t, g t ^ 2 := by
  calc
    _ = ∫ p : ℝ × ℝ, (f p.1 * g p.2) ^ 2 ∂volume.prod volume :=
      (volume_preserving_finTwoArrow ℝ).integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding _
    _ = _ := by simp_rw [mul_pow]; exact integral_prod_mul (fun s : ℝ => f s ^ 2) (fun t : ℝ => g t ^ 2)

/-- Spatial shift/reflection and dilation have the exact scalar L² Jacobian. -/
theorem integral_q3_scaled_sq (L : {l : ℝ // 0 < l}) (r : Fin 4) (x : ℝ) :
    (∫ y, q3Derivative r ((x - y) / L.1) ^ 2) = L.1 * q3DerivativeMoment r := by
  rw [integral_sub_left_eq_self (fun z => q3Derivative r (z / L.1) ^ 2) volume x,
    Measure.integral_comp_div (fun z => q3Derivative r z ^ 2) L.1,
    abs_of_pos L.2, smul_eq_mul, q3Derivative_integral_sq]

/-- Each scaled derivative section is an actual L² class, not just a formal covariance term. -/
theorem memLp_q3_scaled (L : {l : ℝ // 0 < l}) (r : Fin 4) (x : ℝ) :
    MemLp (fun y => q3Derivative r ((x - y) / L.1)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    ((q3Derivative_measurable r).comp ((measurable_const.sub measurable_id).div_const L.1)).aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  change (∫ y, q3Derivative r ((x - y) / L.1) ^ 2) ≠ 0
  rw [integral_q3_scaled_sq]
  exact (mul_pos L.2 (q3DerivativeMoment_pos r)).ne'

/-- Physical derivative kernel: the initial L⁻¹ is the white-noise dimension-two factor. -/
noncomputable def q3SectionFunction (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (x y : Vec 2) : ℝ :=
  (b / L.1 ^ (1 + a.1.1.val + a.1.2.val)) *
    (q3Derivative a.1.1 ((x 0 - y 0) / L.1) *
      q3Derivative a.1.2 ((x 1 - y 1) / L.1))

theorem q3SectionFunction_memLp (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index) (x : Vec 2) :
    MemLp (q3SectionFunction b L a x) 2 volume :=
  by
  unfold q3SectionFunction
  exact (memLp_tensor
    ((q3Derivative_measurable a.1.1).comp ((measurable_const.sub measurable_id).div_const L.1))
    ((q3Derivative_measurable a.1.2).comp ((measurable_const.sub measurable_id).div_const L.1))
    (memLp_q3_scaled L a.1.1 (x 0)) (memLp_q3_scaled L a.1.2 (x 1))).const_mul (b / L.1 ^ (1 + a.1.1.val + a.1.2.val))

/-- The genuine Hilbert-space kernel section, with its explicit pointwise representative. -/
noncomputable def q3Section (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (x : Vec 2) : WhiteNoise :=
  (q3SectionFunction_memLp b L a x).toLp (q3SectionFunction b L a x)

theorem gaussQ3Section_norm_sq (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index) (x : Vec 2) :
    ‖q3Section b L a x‖ ^ 2 =
      (b / L.1 ^ (1 + a.1.1.val + a.1.2.val)) ^ 2 *
        (L.1 * q3DerivativeMoment a.1.1) * (L.1 * q3DerivativeMoment a.1.2) := by
  rw [l2_norm_sq]
  have he : q3Section b L a x =ᵐ[volume] q3SectionFunction b L a x :=
    (q3SectionFunction_memLp b L a x).coeFn_toLp
  calc
    (∫ y, ‖q3Section b L a x y‖ ^ 2) = ∫ y, (q3SectionFunction b L a x y) ^ 2 :=
      integral_congr_ae (he.mono fun y hy => by dsimp only; rw [hy, Real.norm_eq_abs, sq_abs])
    _ = _ := by
      simp only [q3SectionFunction, mul_pow]
      rw [integral_const_mul]
      simp_rw [← mul_pow]
      rw [integral_tensor_sq (fun s => q3Derivative a.1.1 ((x 0 - s) / L.1))
        (fun t => q3Derivative a.1.2 ((x 1 - t) / L.1)),
        integral_q3_scaled_sq, integral_q3_scaled_sq]
      ring

/-- Translation continuity is in L², so it also covers the discontinuous third derivative. -/
theorem q3Section_continuous (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index) :
    Continuous (q3Section b L a) := by
  let g : Vec 2 → C(Vec 2, Vec 2) := fun x => ⟨fun y => y + -x,
    continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst.neg)
  have hgm : ∀ x, MeasurePreserving (g x) volume volume :=
    fun x => measurePreserving_add_right volume (-x)
  have hc := (continuous_const (y := q3Section b L a 0)).compMeasurePreservingLp
    hg hgm (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have he (x : Vec 2) :
      Lp.compMeasurePreserving (g x) (hgm x) (q3Section b L a 0) =
        q3Section b L a x := by
    apply Lp.ext
    have h0 := (q3SectionFunction_memLp b L a 0).coeFn_toLp
    have hx := (q3SectionFunction_memLp b L a x).coeFn_toLp
    have ht := (hgm x).quasiMeasurePreserving.ae h0
    filter_upwards [Lp.coeFn_compMeasurePreserving (q3Section b L a 0) (hgm x), ht, hx]
      with y hy hty hxy
    change (q3Section b L a x) y = q3SectionFunction b L a x y at hxy
    change (q3Section b L a 0) (g x y) = q3SectionFunction b L a 0 (g x y) at hty
    rw [hy]
    change (q3Section b L a 0) (g x y) = _
    rw [hty, hxy]
    simp [q3SectionFunction, g, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  simpa only [he] using hc

end ASDExplicitGamma.Gaussian
