module

public import ASDExplicitGamma.Native.OldSignedProjectedDerivativeReality
public import ASDExplicitGamma.Native.OldSignedProjectedTrace
public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation

/-! Differentiation of the actual projected-kernel trace recovers the
actual q3 first-derivative white kernel, with the physical shell length. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Scalar
noncomputable section

/-- Evaluating the actual strong derivative in a coordinate gives the
constructed derivative white kernel. -/
theorem old_signed_projected_white_derivative_basis (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j k : Fin 2) :
    ((oldSignedPotentialWhiteMap b L).comp (oldSignedProjectedSpatialDerivative b x i j)) (basisVec k)=
      oldSignedProjectedDerivativeWhiteKernel b L x i j k := by
  fin_cases k <;> simp [ContinuousLinearMap.comp_apply,oldSignedProjectedSpatialDerivative,
    oldSignedProjectedDerivativeWhiteKernel,basisVec]

/-- A scalar test of the trace derivative equals the actual convolution
first derivative. The actual raw convolution differentiability supplies it. -/
theorem old_signed_white_trace_derivative_pairing (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (w : WhiteNoise) (k : Fin 2) :
    inner ℝ w (oldSignedProjectedDerivativeWhiteKernel b L x 0 0 k+
      oldSignedProjectedDerivativeWhiteKernel b L x 1 1 k)=
    L.1*q3Convolution b L (lambda8Q3FirstIndex k) w (L.1 • x) := by
  have hs := (old_signed_projected_white_hasFDerivAt b L x 0 0).add
    (old_signed_projected_white_hasFDerivAt b L x 1 1)
  have hw := (innerSL ℝ w).hasFDerivAt.comp x hs
  have he : (fun y => inner ℝ w (oldSignedProjectedWhiteKernel b L y 0 0+
      oldSignedProjectedWhiteKernel b L y 1 1))=
      (fun y => q3Convolution b L h3Zero w (L.1 • y)) := by
    funext y
    rw [old_signed_projected_white_kernel_trace]
    rfl
  change HasFDerivAt (fun y => inner ℝ w (oldSignedProjectedWhiteKernel b L y 0 0+
    oldSignedProjectedWhiteKernel b L y 1 1)) _ x at hw
  rw [he] at hw
  have hl : HasFDerivAt (fun y : Vec 2 => L.1 • y)
      (L.1 • ContinuousLinearMap.id ℝ (Vec 2)) x := (hasFDerivAt_id x).const_smul L.1
  have hr := (q3Convolution_hasFDerivAt b L h3Zero
    (by norm_num [h3Zero,H3Index]) w (L.1 • x)).comp x hl
  have hh := congrArg (fun D : Vec 2 →L[ℝ] ℝ => D (basisVec k)) (hw.unique hr)
  change inner ℝ w (((oldSignedPotentialWhiteMap b L).comp (oldSignedProjectedSpatialDerivative b x 0 0)) (basisVec k)+
    ((oldSignedPotentialWhiteMap b L).comp (oldSignedProjectedSpatialDerivative b x 1 1)) (basisVec k))=_ at hh
  rw [old_signed_projected_white_derivative_basis,old_signed_projected_white_derivative_basis] at hh
  fin_cases k <;> simpa [ContinuousLinearMap.comp_apply,lambda8Q3FirstIndex,basisVec,Pi.single_apply,
    h3Zero,H3Index] using hh

/-- The actual white vector identity is recovered from all its scalar
tests. The dimensionless derivative carries exactly one shell-length factor. -/
theorem old_signed_white_trace_derivative (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (k : Fin 2) :
    oldSignedProjectedDerivativeWhiteKernel b L x 0 0 k+
      oldSignedProjectedDerivativeWhiteKernel b L x 1 1 k=
      L.1 • q3Section b L (lambda8Q3FirstIndex k) (L.1 • x) := by
  apply ext_inner_left ℝ
  intro w
  rw [real_inner_smul_right]
  exact old_signed_white_trace_derivative_pairing b L x w k

end
end ASDExplicitGamma.Native
