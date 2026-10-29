module

public import ASDExplicitGamma.Gaussian.SupMeanFirstMoments
public import ASDExplicitGamma.Gaussian.SupMeanSecondMoments

/-! The scalar observation tensors are exactly the full stored planar matrix tensors. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise BigOperators
noncomputable section

/-- The fixed skew-matrix embedding, retaining every matrix entry. -/
def supMeanSkewEmbedding : ℝ →L[ℝ] Mat 2 where
  toFun t := fun a b => t*q3SkewEntry a b
  map_add' s t := by ext a b; change (s+t)*_ = s*_+t*_; ring
  map_smul' c t := by ext a b; change (c*t)*_ = c*(t*_); ring
  cont := by fun_prop

/-- Every planar shell is its scalar stream times the fixed skew matrix. -/
theorem supMean_shell_skew_embedding (j : ShellField 2) (x : Vec 2) :
    j x = supMeanSkewEmbedding (shellScalarValue j x) := by
  have h0 := j.skew_entry x 0 0
  have h1 := j.skew_entry x 1 1
  have h01 := j.skew_entry x 0 1
  ext a b
  change j x a b = j x 1 0*q3SkewEntry a b
  fin_cases a <;> fin_cases b <;> norm_num [q3SkewEntry] <;> linarith only [h0,h1,h01]

end
end ASDExplicitGamma.Gaussian
