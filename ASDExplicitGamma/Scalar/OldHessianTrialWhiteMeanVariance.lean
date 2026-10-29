module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovarianceKernel
public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCentering

/-! The actual white section as a genuine Hilbert H1 field, with its
physical derivative variance and sharp cube mean-oscillation bound. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Every white section has its true constant pointwise norm, hence is
bounded on any measure without a spatial supremum hypothesis. -/
theorem old_hessian_white_section_memLp_top (mu : Measure (Vec 2)) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : H3Index) : MemLp (q3Section b L a) ⊤ mu := by
  apply memLp_top_of_bound (q3Section_continuous b L a).aestronglyMeasurable
    ‖q3Section b L a 0‖
  filter_upwards with x
  apply le_of_eq
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gaussQ3Section_norm_sq,gaussQ3Section_norm_sq]

/-- The jet used in the actual multiplier is the physical first section. -/
theorem old_hessian_first_jet_index (i : Fin 2) :
    mainQ3JetIndex (.first i)=lambda8Q3FirstIndex i := by
  fin_cases i <;> norm_num [mainQ3JetIndex,Model.Q3SpatialJet.count,lambda8Q3FirstIndex,h3Next,h3Zero,H3Index]

/-- The physical white section has the actual scalar convolution weak
derivative in every white direction, not an assigned Hilbert gradient. -/
def oldHessianWhiteSectionH1 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    HilbertH1Function (openCubeSet Q) WhiteNoise where
  toFun := q3Section b L h3Zero
  grad x i := q3Section b L (mainQ3JetIndex (.first i)) x
  memL2 := (old_hessian_white_section_memLp_top _ b L h3Zero).mono_exponent (by simp)
  gradMemL2 i := (old_hessian_white_section_memLp_top _ b L (mainQ3JetIndex (.first i))).mono_exponent (by simp)
  hasWeakGradient w := by
    let u := (mainQ3DirectionW2 Q b L w).value
    have hv : (fun x => inner ℝ w (q3Section b L h3Zero x))=u.toFun := by
      funext x
      exact (mainQ3DirectionW2_value Q b L w x).symm
    have hg : (fun x i => inner ℝ w (q3Section b L (mainQ3JetIndex (.first i)) x))=u.grad := by
      funext x i
      exact (mainQ3DirectionW2_jet Q b L w (.first i) x).symm
    rw [hv,hg]
    exact u.hasWeakGradient

/-- Exact derivative energy of the same genuine Hilbert H1 section. -/
theorem old_hessian_white_h1_gradient_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    hilbertGradientEnergy Q (oldHessianWhiteSectionH1 Q b L).grad=mainFlatSigmaSq b L := by
  have he (i : Fin 2) : hilbertEnergy Q (q3Section b L (mainQ3JetIndex (.first i)))=
      ‖q3Section b L (mainQ3JetIndex (.first i)) 0‖^2 := by
    simp only [hilbertEnergy,gaussQ3Section_norm_sq,integral_const,Measure.real_def,
      normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul]
  change (∑ i : Fin 2,hilbertEnergy Q (q3Section b L (mainQ3JetIndex (.first i))))=_
  simp_rw [he,old_hessian_first_jet_index,←old_signed_white_section_derivative]
  exact old_signed_white_section_gradient_norm b L 0

/-- Sharp physical coefficient cell-mean variance, with the complete white
covariance summed before the Poincare payment. -/
theorem old_hessian_white_mean_variance (U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    hilbertEnergy U (fun x => q3Section b L h3Zero x-
      hilbertCubeAverage U (q3Section b L h3Zero)) ≤
        (cubeScaleFactor U/Real.pi)^2*mainFlatSigmaSq b L := by
  have hh := hilbert_cube_poincare U (oldHessianWhiteSectionH1 U b L)
  rw [old_hessian_white_h1_gradient_energy] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
