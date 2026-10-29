module

public import ASDExplicitGamma.Gaussian.GeneratorAlgebra
public import ASDExplicitGamma.Gaussian.C2Averaging

/-! # Covariance contraction as a bounded linear functional on Hessians -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))

include hH in
private theorem summable_bilinear_diagonal (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Summable (fun j => B (H j) (H j)) :=
  summable_bilinear_images hH B (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)

include hH in
theorem norm_bilinear_diagonal_tsum (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖∑' j, B (H j) (H j)‖ ≤ (∑' j, ‖H j‖ ^ 2) * ‖B‖ := by
  have hb (j : ℕ) : ‖B (H j) (H j)‖ ≤ ‖B‖ * ‖H j‖ ^ 2 := by
    simpa only [pow_two, mul_assoc] using B.le_opNorm₂ (H j) (H j)
  have hs := summable_bilinear_diagonal H hH B
  have h := (norm_tsum_le_tsum_norm hs.norm).trans
    (hs.norm.tsum_le_tsum hb (hH.mul_left ‖B‖))
  rw [tsum_mul_left] at h
  exact h.trans_eq (mul_comm _ _)

/-- A covariance trace is a bounded linear functional on the space of bounded bilinear forms.
Its meaning is the absolutely convergent directional trace; its norm is at most Σ‖H_j‖². -/
noncomputable def bilinearTraceMap : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun (B : E →L[ℝ] E →L[ℝ] ℝ) => ∑' j, B (H j) (H j)
      map_add' := fun B C => by
        simp only [add_apply]
        exact (summable_bilinear_diagonal H hH B).tsum_add
          (summable_bilinear_diagonal H hH C)
      map_smul' := fun a B => by
        simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
    (∑' j, ‖H j‖ ^ 2) (norm_bilinear_diagonal_tsum H hH)

@[simp] theorem bilinearTraceMap_apply (B : E →L[ℝ] E →L[ℝ] ℝ) :
    bilinearTraceMap H hH B = ∑' j, B (H j) (H j) := rfl

/-- The covariance contraction of a C² test is precisely the Hessian trace functional. -/
theorem modelCovarianceTrace_eq_bilinearTraceMap {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    modelCovarianceTrace f H x = bilinearTraceMap H hH (fderiv ℝ (fderiv ℝ f) x) := by
  apply tsum_congr
  intro j
  exact second_fderiv_eq hf x (H j) (H j)

include hH in
/-- Covariance contraction commutes with an independent average. This is an absolute
Bochner integral interchange on Hessians, rather than a formal exchange of infinite sums. -/
theorem covarianceTrace_integral_translate {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → E) (hZ : StronglyMeasurable Z)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖Z ω‖) ^ d) μ)
    {f : E → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) (x : E) :
    modelCovarianceTrace (fun y => ∫ ω, f (y + Z ω) ∂μ) H x =
      ∫ ω, modelCovarianceTrace f H (x + Z ω) ∂μ := by
  have hsmooth := c2_integral_translate μ Z hZ hMom hf
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH hsmooth.1,
    hsmooth.2.2 x]
  obtain ⟨C, hC, d, hb⟩ := polynomial_c2_jet_bound hf
  have hd : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.1.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  let bilinearNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let bilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  have hi : Integrable (fun ω => fderiv ℝ (fderiv ℝ f) (x + Z ω)) μ := by
    let B : ℝ := C * (2 + ‖x‖) ^ d
    apply ((hMom d).const_mul B).mono'
      (hd.comp_stronglyMeasurable (stronglyMeasurable_const.add hZ)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      have htri := norm_add_le x (Z ω)
      have harg : 1 + ‖x + Z ω‖ ≤ (2 + ‖x‖) * (1 + ‖Z ω‖) := by
        nlinarith [norm_nonneg x, norm_nonneg (Z ω), mul_nonneg (norm_nonneg x) (norm_nonneg (Z ω))]
      have hval : ‖fderiv ℝ (fderiv ℝ f) (x + Z ω)‖ ≤ C * (1 + ‖x + Z ω‖) ^ d := by
        have h := hb (x + Z ω)
        linarith [abs_nonneg (f (x + Z ω)), norm_nonneg (fderiv ℝ f (x + Z ω))]
      exact hval.trans (by
        have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) harg d) hC
        simpa only [B, mul_pow, mul_assoc] using h)
  rw [← (bilinearTraceMap H hH).integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => (modelCovarianceTrace_eq_bilinearTraceMap H hH hf.1 (x + Z ω)).symm

end
end ASDExplicitGamma.Gaussian
