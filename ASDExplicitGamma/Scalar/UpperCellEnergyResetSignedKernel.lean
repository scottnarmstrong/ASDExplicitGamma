module

public import Algsuperdiff.Section3.Provider.Corrector.GradientIdentification

-- Adapted from the Algsuperdiff gradient-identification development
-- (Apache-2.0), removing positivity and normalization of the spatial kernel.
/-! Strong horizontal derivatives tested against arbitrary signed smooth
compact kernels, as required by the physical weak-gradient identity. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector
noncomputable section

section Orbit

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The mollified field is differentiable along every coordinate orbit, with
derivative the mollification by the corresponding partial derivative of the
kernel.  This is the pointwise half of the gradient identification. -/
theorem upper_cell_reset_signed_kernel_orbit (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ) (i : Fin d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    ∀ᵐ ω ∂μ, HasDerivAt (fun t : ℝ => mollify κ φ ((t • basisVec i) +ᵥ ω))
      (mollify (kernelDeriv κ i) φ ω) 0 := by
  filter_upwards [ae_locallyIntegrable_realize (d := d) (μ := μ) hφm hφ] with ω hloc
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (realize (d := d) (mollify κ φ) ω) := by
    rw [realize_mollify]
    exact hc.contDiff_convolution_left _ hκ hloc
  have hpt : ((0 : ℝ) • (basisVec i : Vec d)) = 0 := zero_smul _ _
  have hfd : HasFDerivAt (realize (d := d) (mollify κ φ) ω)
      (fderiv ℝ (realize (d := d) (mollify κ φ) ω) ((0 : ℝ) • (basisVec i : Vec d)))
      ((0 : ℝ) • (basisVec i : Vec d)) :=
    (hsmooth.differentiable (by simp) _).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • (basisVec i : Vec d)) (basisVec i) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (basisVec i : Vec d)
  have hcomp := hfd.comp_hasDerivAt (0 : ℝ) hline
  rw [hpt] at hcomp
  have hval : fderiv ℝ (realize (d := d) (mollify κ φ) ω) 0 (basisVec i)
      = mollify (kernelDeriv κ i) φ ω := by
    rw [fderiv_realize_mollify hc hκ hloc 0 i,
      realize_mollifyGrad_toVec, realize_apply, zero_vadd]
  rw [hval] at hcomp
  exact hcomp

end Orbit

section DiffQuot

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- The difference quotient of a stationary field along the `i`th coordinate
orbit at scale `t`. -/
private def diffQuot (i : Fin d) (t : ℝ) (φ : Ω → ℝ) (ω : Ω) : ℝ :=
  t⁻¹ • (φ ((t • basisVec i) +ᵥ ω) - φ ω)

end DiffQuot

section DiffQuotLp

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω}
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

omit [VAddInvariantMeasure (Vec d) Ω μ] in
private theorem stronglyMeasurable_diffQuot (i : Fin d) (t : ℝ) {φ : Ω → ℝ}
    (hφm : StronglyMeasurable φ) : StronglyMeasurable (diffQuot (Ω := Ω) i t φ) :=
  ((hφm.comp_measurable (measurable_const_vadd (t • basisVec i))).sub hφm).const_smul (t⁻¹ : ℝ)

private theorem memLp_diffQuot (i : Fin d) (t : ℝ) {φ : Ω → ℝ} (hφ : MemLp φ 2 μ) :
    MemLp (diffQuot (Ω := Ω) i t φ) 2 μ :=
  ((hφ.comp_measurePreserving
    (measurePreserving_const_vadd (μ := μ) (t • basisVec i))).sub hφ).const_smul (t⁻¹ : ℝ)

/-- The difference quotient is represented in `L²` by the corresponding
difference quotient of the Koopman orbit. -/
private theorem integral_normSq_diffQuot_sub_eq (i : Fin d) (t : ℝ)
    {φ : Ω → ℝ} (hφ : MemLp φ 2 μ) {G : Ω → ℝ} (hG : MemLp G 2 μ) :
    ∫ ω, ‖diffQuot i t φ ω - G ω‖ ^ 2 ∂μ
      = ‖t⁻¹ • (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ)
          - hG.toLp G‖ ^ 2 := by
  rw [norm_sq_eq_integral_normSq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub
      (t⁻¹ • (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ)) (hG.toLp G),
    Lp.coeFn_smul (t⁻¹ : ℝ) (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ),
    Lp.coeFn_sub (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ)) (hφ.toLp φ),
    coeFn_koopman_toLp hφ (t • basisVec i), hφ.coeFn_toLp, hG.coeFn_toLp]
    with ω h1 h2 h3 h4 h5 h6
  rw [h1]
  simp only [Pi.sub_apply, h2, Pi.smul_apply, h3, h4, h5, h6]
  rfl

end DiffQuotLp

/-! ### The gradient identification -/

section Identification

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- The sequence of scales along which the difference quotients are taken. -/
private def quotScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

private theorem quotScale_pos (n : ℕ) : 0 < quotScale n := by
  unfold quotScale; positivity

private theorem tendsto_quotScale :
    Filter.Tendsto quotScale Filter.atTop (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) := by
  have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Filter.Tendsto quotScale Filter.atTop (nhds (0 : ℝ)) := by
    refine h.congr fun n => ?_
    rw [quotScale, one_div]
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within quotScale hlim ?_
  exact Filter.Eventually.of_forall fun n => (quotScale_pos n).ne'

omit [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω] in
/-- The difference quotients converge to the strong horizontal derivative in
`L²(Ω)`. -/
private theorem tendsto_integral_normSq_diffQuot_sub (i : Fin d)
    {φ : Ω → ℝ} (hφ : MemLp φ 2 μ) {G : Ω → ℝ} (hG : MemLp G 2 μ)
    (hderiv : HasDerivAt (fun t : ℝ => koopman (μ := μ) (t • basisVec i) (hφ.toLp φ))
      (hG.toLp G) 0) :
    Filter.Tendsto (fun n : ℕ => ∫ ω, ‖diffQuot i (quotScale n) φ ω - G ω‖ ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
  have hf0 : koopman (μ := μ) ((0 : ℝ) • (basisVec i : Vec d)) (hφ.toLp φ) = hφ.toLp φ := by
    rw [zero_smul, koopman_zero]
  have hslope : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (koopman (μ := μ) (t • basisVec i) (hφ.toLp φ) - hφ.toLp φ))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (hG.toLp G)) := by
    have hthis := hasDerivAt_iff_tendsto_slope.1 hderiv
    simpa only [slope_fun_def, vsub_eq_sub, sub_zero, hf0] using hthis
  have hQtend : Filter.Tendsto
      (fun n : ℕ => (quotScale n)⁻¹ •
        (koopman (μ := μ) (quotScale n • basisVec i) (hφ.toLp φ) - hφ.toLp φ))
      Filter.atTop (nhds (hG.toLp G)) := hslope.comp tendsto_quotScale
  have hnorm : Filter.Tendsto (fun n : ℕ =>
      ‖(quotScale n)⁻¹ •
        (koopman (μ := μ) (quotScale n • basisVec i) (hφ.toLp φ) - hφ.toLp φ)
        - hG.toLp G‖ ^ 2) Filter.atTop (nhds 0) := by
    simpa using ((hQtend.sub_const (hG.toLp G)).norm).pow 2
  refine hnorm.congr fun n => ?_
  exact (integral_normSq_diffQuot_sub_eq i (quotScale n) hφ hG).symm

/-- The mollified difference quotients converge pointwise to the mollification
by the corresponding partial derivative of the kernel. -/
private theorem ae_tendsto_mollify_diffQuot (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ) (i : Fin d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n : ℕ => mollify κ (diffQuot i (quotScale n) φ) ω) Filter.atTop
      (nhds (mollify (kernelDeriv κ i) φ ω)) := by
  have hintφ : ∀ᵐ ω ∂μ, Integrable (fun y => κ y • φ ((-y) +ᵥ ω)) volume :=
    ae_integrable_smul_comp_vadd (μ := μ) hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc) hφm hφ
  have hintshift : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      Integrable (fun y =>
        κ y • φ ((quotScale n • basisVec i) +ᵥ ((-y) +ᵥ ω))) volume := by
    refine ae_all_iff.2 fun n => ?_
    exact ae_integrable_smul_comp_vadd (μ := μ)
      (X := fun ω => φ ((quotScale n • basisVec i) +ᵥ ω)) hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc)
      (hφm.comp_measurable (measurable_const_vadd (quotScale n • basisVec i)))
      (hφ.comp_measurePreserving
        (measurePreserving_const_vadd (μ := μ) (quotScale n • basisVec i)))
  filter_upwards [hintφ, hintshift,
    upper_cell_reset_signed_kernel_orbit (μ := μ) κ hκ hc i hφm hφ] with ω h0 hn hderiv'
  have heq : ∀ n : ℕ, mollify κ (diffQuot i (quotScale n) φ) ω
      = (quotScale n)⁻¹ • (mollify κ φ ((quotScale n • basisVec i) +ᵥ ω)
        - mollify κ φ ω) := by
    intro n
    show mollify κ (fun ω' =>
        (quotScale n)⁻¹ • (φ ((quotScale n • basisVec i) +ᵥ ω') - φ ω')) ω = _
    rw [mollify_smul κ ((quotScale n)⁻¹ : ℝ)
        (fun ω' => φ ((quotScale n • basisVec i) +ᵥ ω') - φ ω') ω,
      mollify_sub (hn n) h0, mollify_comp_vadd]
  have hg0 : mollify κ φ (((0 : ℝ) • (basisVec i : Vec d)) +ᵥ ω)
      = mollify κ φ ω := by
    rw [zero_smul, zero_vadd]
  have hs : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (mollify κ φ ((t • basisVec i) +ᵥ ω) - mollify κ φ ω))
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) (nhds (mollify (kernelDeriv κ i) φ ω)) := by
    have hthis := hasDerivAt_iff_tendsto_slope.1 hderiv'
    simpa only [slope_fun_def, vsub_eq_sub, sub_zero, hg0] using hthis
  exact (hs.comp tendsto_quotScale).congr fun n => (heq n).symm

/-- **Componentwise gradient identification.**  If the coordinate orbit of `φ`
has strong `L²` derivative `G` at the origin, then mollifying `φ` by the `i`th
partial derivative of the kernel is the same as mollifying `G` by the kernel. -/
theorem upper_cell_reset_signed_kernel_derivative (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ) (i : Fin d)
    {φ : Ω → ℝ} (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    {G : Ω → ℝ} (hGm : StronglyMeasurable G) (hG : MemLp G 2 μ)
    (hderiv : HasDerivAt (fun t : ℝ => koopman (μ := μ) (t • basisVec i) (hφ.toLp φ))
      (hG.toLp G) 0) :
    mollify (kernelDeriv κ i) φ =ᵐ[μ] mollify κ G := by
  have hDm : ∀ n : ℕ, StronglyMeasurable (diffQuot (Ω := Ω) i (quotScale n) φ) := fun n =>
    stronglyMeasurable_diffQuot i (quotScale n) hφm
  have hDL : ∀ n : ℕ, MemLp (diffQuot (Ω := Ω) i (quotScale n) φ) 2 μ := fun n =>
    memLp_diffQuot (μ := μ) i (quotScale n) hφ
  have hZm : ∀ n : ℕ, StronglyMeasurable
      fun ω => diffQuot (Ω := Ω) i (quotScale n) φ ω - G ω := fun n => (hDm n).sub hGm
  have hZL : ∀ n : ℕ, MemLp
      (fun ω => diffQuot (Ω := Ω) i (quotScale n) φ ω - G ω) 2 μ := fun n => (hDL n).sub hG
  have hcontr : ∀ n : ℕ,
      ∫ ω, ‖mollify κ (diffQuot i (quotScale n) φ) ω - mollify κ G ω‖ ^ 2 ∂μ
        ≤ (∫ y, |κ y|) ^ 2 * ∫ ω, ‖diffQuot i (quotScale n) φ ω - G ω‖ ^ 2 ∂μ := by
    intro n
    have hsub : ∀ᵐ ω ∂μ,
        mollify κ (fun ω' => diffQuot i (quotScale n) φ ω' - G ω') ω
          = mollify κ (diffQuot i (quotScale n) φ) ω - mollify κ G ω := by
      filter_upwards [ae_integrable_smul_comp_vadd (μ := μ) hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc)
          (hDm n) (hDL n),
        ae_integrable_smul_comp_vadd (μ := μ) hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc) hGm hG] with ω h1 h2
      exact mollify_sub h1 h2
    have hbase := integral_normSq_mollify_le (μ := μ) hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc)
      (hZm n) (hZL n)
    refine le_trans (le_of_eq ?_) hbase
    exact (integral_congr_ae (by filter_upwards [hsub] with ω hω; rw [hω])).symm
  have hL2 := tendsto_integral_normSq_diffQuot_sub (μ := μ) i hφ hG hderiv
  have hAL2 : Filter.Tendsto (fun n : ℕ =>
      ∫ ω, ‖mollify κ (diffQuot i (quotScale n) φ) ω - mollify κ G ω‖ ^ 2 ∂μ)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => integral_nonneg fun ω => by positivity) hcontr ?_
    simpa using hL2.const_mul ((∫ y, |κ y|) ^ 2)
  have hmemA : ∀ n : ℕ, MemLp (mollify κ (diffQuot (Ω := Ω) i (quotScale n) φ)) 2 μ :=
    fun n => memLp_two_mollify hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc) (hDm n) (hDL n)
  have hmemC : MemLp (mollify κ G) 2 μ :=
    memLp_two_mollify hκ.continuous (hκ.continuous.integrable_of_hasCompactSupport hc) hGm hG
  have hmemB : MemLp (mollify (kernelDeriv κ i) φ) 2 μ :=
    memLp_two_mollify (continuous_kernelDeriv hκ i)
      (integrable_kernelDeriv hc hκ i) hφm hφ
  refine ae_eq_of_tendsto_of_tendsto_integral_normSq
    (fun n => (hmemA n).aestronglyMeasurable) hmemB.aestronglyMeasurable
    hmemC.aestronglyMeasurable (ae_tendsto_mollify_diffQuot (μ := μ) κ hκ hc i hφm hφ)
    (fun n => ?_) hAL2
  have hd : MemLp (fun ω =>
      mollify κ (diffQuot (Ω := Ω) i (quotScale n) φ) ω - mollify κ G ω) 2 μ :=
    (hmemA n).sub hmemC
  exact (memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd

end Identification

end
end ASDExplicitGamma.Scalar
