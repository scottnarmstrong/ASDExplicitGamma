module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovarianceKernel
public import ASDExplicitGamma.Triadic.HilbertL2Bounds
public import Mathlib.MeasureTheory.Function.L2Space

/-! Exact covariance freezing in the physical normalized cell measure.
The cell oscillation remains an explicit joint pairing of both kernels. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Actual Hilbert covariance integrability follows from the L2 kernels. -/
theorem old_hessian_hilbert_pairing_integrable {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (F G : Vec 2 → E)
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    Integrable (fun x => inner ℝ (F x) (G x)) (normalizedCubeMeasure Q) := by
  exact (hF.norm.integrable_mul hG.norm).mono'
    (hF.aestronglyMeasurable.inner hG.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => norm_inner_le_norm (F x) (G x)))

/-- Constant-one Hilbert L2 covariance Cauchy on the actual cell. -/
theorem old_hessian_hilbert_pairing_cauchy {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (F G : Vec 2 → E)
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x => inner ℝ (F x) (G x))| ≤
      Real.sqrt (hilbertEnergy Q F)*Real.sqrt (hilbertEnergy Q G) := by
  have hc := abs_pairing_le Q hF.norm hG.norm
  simp only [l2Norm,hilbertEnergy_norm,pairing,cubeAverage_eq_integral_normalizedCubeMeasure] at hc
  have hi := (hF.norm.integrable_mul hG.norm)
  have hm : (∫ x,|inner ℝ (F x) (G x)| ∂normalizedCubeMeasure Q) ≤
      ∫ x,‖F x‖*‖G x‖ ∂normalizedCubeMeasure Q := by
    exact integral_mono_ae (old_hessian_hilbert_pairing_integrable Q F G hF hG).norm hi
      (Filter.Eventually.of_forall (fun x => abs_real_inner_le_norm (F x) (G x)))
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    _ ≤ ∫ x,|inner ℝ (F x) (G x)| ∂normalizedCubeMeasure Q := abs_integral_le_integral_abs
    _ ≤ ∫ x,‖F x‖*‖G x‖ ∂normalizedCubeMeasure Q := hm
    _ ≤ _ := (le_abs_self _).trans hc

/-- The exact mean covariance equals the full contraction minus the joint
centered contraction; no centered receiver or kernel is discarded. -/
theorem old_hessian_hilbert_covariance_centering {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (F G : Vec 2 → E)
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) (hG : MemLp G 2 (normalizedCubeMeasure Q)) :
    inner ℝ (hilbertCubeAverage Q F) (hilbertCubeAverage Q G)=
      cubeAverage Q (fun x => inner ℝ (F x) (G x))-
        cubeAverage Q (fun x => inner ℝ (F x-hilbertCubeAverage Q F) (G x-hilbertCubeAverage Q G)) := by
  let f := hilbertCubeAverage Q F
  let g := hilbertCubeAverage Q G
  have hf : Integrable F (normalizedCubeMeasure Q) := hF.integrable (by norm_num)
  have hg : Integrable G (normalizedCubeMeasure Q) := hG.integrable (by norm_num)
  have hfg := old_hessian_hilbert_pairing_integrable Q F G hF hG
  have hFc := hf.inner_const (𝕜 := ℝ) g
  have hcG := hg.const_inner (𝕜 := ℝ) f
  have h1 : (∫ x,inner ℝ (F x) g ∂normalizedCubeMeasure Q)=inner ℝ f g := by
    change _=inner ℝ (∫ x,F x ∂normalizedCubeMeasure Q) g
    simpa only [real_inner_comm g] using integral_inner hf g
  have h2 : (∫ x,inner ℝ f (G x) ∂normalizedCubeMeasure Q)=inner ℝ f g := integral_inner hg f
  have he (x : Vec 2) : inner ℝ (F x-f) (G x-g)=
      inner ℝ (F x) (G x)-inner ℝ (F x) g-inner ℝ f (G x)+inner ℝ f g := by
    simp only [inner_sub_left,inner_sub_right]
    ring
  change inner ℝ f g=cubeAverage Q _-cubeAverage Q (fun x => inner ℝ (F x-f) (G x-g))
  simp_rw [he]
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsub1 := integral_sub hfg hFc
  have hsub2 := integral_sub (hfg.sub hFc) hcG
  have hadd := integral_add ((hfg.sub hFc).sub hcG)
    (show Integrable (fun _ : Vec 2 => inner ℝ f g) (normalizedCubeMeasure Q) from integrable_const _)
  simp only [Pi.sub_apply,Pi.add_apply] at hsub1 hsub2 hadd
  rw [hadd,hsub2,hsub1,h1,h2]
  simp only [integral_const,Measure.real_def,normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul]
  ring

end
end ASDExplicitGamma.Scalar
