module

public import ASDExplicitGamma.Native.OldSignedRowMultiplier
public import ASDExplicitGamma.Native.OldSignedProjectedDerivativeEnergy
public import ASDExplicitGamma.Main.FlatFieldH1Bounds

/-! The actual q3 white covariance row is C1, with its exact variance and
first-derivative variance. These are coefficient facts, not trial estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Scalar ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- The physical white section is a genuinely C1 Hilbert-valued field. -/
theorem old_signed_white_section_contDiff (b : ℝ) (L : {l : ℝ // 0 < l}) :
    ContDiff ℝ 1 (q3Section b L h3Zero) := by
  have hs : ContDiff ℝ 1 (fun x : Vec 2 => L.1⁻¹ • x) :=
    (L.1⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).contDiff
  have hc i j : ContDiff ℝ 1 (fun x : Vec 2 =>
      oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j) :=
    (oldSignedPotentialWhiteMap b L).contDiff.comp ((old_signed_projected_character_contDiff b i j).comp hs)
  have he : q3Section b L h3Zero=(fun x =>
      oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) 0 0+
      oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) 1 1) := by
    funext x
    rw [old_signed_projected_white_kernel_trace]
    congr 1
    simp only [smul_smul,mul_inv_cancel₀ L.2.ne',one_smul]
  rw [he]
  exact (hc 0 0).add (hc 1 1)

/-- The actual derivative of the physical white section, not an assigned
jet, equals the corresponding q3 derivative section. -/
theorem old_signed_white_section_derivative (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (k : Fin 2) :
    (fderiv ℝ (q3Section b L h3Zero) x) (basisVec k)=
      q3Section b L (lambda8Q3FirstIndex k) x := by
  apply ext_inner_left ℝ
  intro w
  let l : WhiteNoise →L[ℝ] ℝ := innerSL ℝ w
  have hs := l.hasFDerivAt.comp x
    ((old_signed_white_section_contDiff b L).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have ht := q3Convolution_hasFDerivAt b L h3Zero
    (by norm_num [h3Zero,H3Index]) w x
  have he : (fun y => l (q3Section b L h3Zero y))=
      (fun y => q3Convolution b L h3Zero w y) := by
    funext y
    rfl
  have hh := hs
  change HasFDerivAt (fun y => l (q3Section b L h3Zero y)) _ x at hh
  rw [he] at hh
  have hv := congrArg (fun D : Vec 2 →L[ℝ] ℝ => D (basisVec k)) (hh.unique ht)
  fin_cases k <;> simpa [ContinuousLinearMap.comp_apply,l,innerSL_apply_apply,
    lambda8Q3FirstIndex,basisVec,Pi.single_apply,h3Zero,H3Index,q3Convolution] using hv


/-- Exact physical first-derivative variance in the source normalization. -/
theorem old_signed_white_section_gradient_norm (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ k : Fin 2,‖(fderiv ℝ (q3Section b L h3Zero) x) (basisVec k)‖^2)=
      mainFlatSigmaSq b L := by
  simp_rw [old_signed_white_section_derivative,gaussQ3Section_norm_sq]
  norm_num [Fin.sum_univ_two,lambda8Q3FirstIndex,h3Next,h3Zero,H3Index,
    q3DerivativeMoment,mainFlatSigmaSq]
  field_simp [L.2.ne']
  ring

end
end ASDExplicitGamma.Native
