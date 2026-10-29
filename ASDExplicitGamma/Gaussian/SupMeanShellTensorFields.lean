module

public import ASDExplicitGamma.Gaussian.SupMeanShellKernel
public import ASDExplicitGamma.Gaussian.SupMeanSkewTensor

/-! Actual continuous tensor fields on the frozen shell carrier, with genuine pointwise integrability. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Every stored coordinate jet is a continuous spatial field for each shell. -/
theorem supMean_shell_jet_spatial_continuous (o : Q3SpatialJet) (j : ShellField 2) :
    Continuous (fun x => shellDerivativeEval (supMeanJetObservation o x) j) := by
  cases o with
  | value =>
    exact shellScalarEntry.continuous.comp j.val.1.continuous
  | first i =>
    exact (shellScalarEntry.comp (ContinuousLinearMap.apply ℝ (Mat 2) (basisVec i))).continuous.comp j.deriv.continuous
  | second i k =>
    exact ((shellScalarEntry.comp (ContinuousLinearMap.apply ℝ (Mat 2) (basisVec i))).comp
      (ContinuousLinearMap.apply ℝ (Vec 2 →L[ℝ] Mat 2) (basisVec k))).continuous.comp j.secondDeriv.continuous

/-- The literal finite tensor field, retaining the full skew Frobenius factor. -/
def supMeanShellTensor {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) (j : ShellField 2) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => supMeanShellJetScalar (o i) x j)

/-- Continuity in the actual spatial variable. -/
theorem supMean_shell_tensor_spatial_continuous {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) (j : ShellField 2) : Continuous (fun x => supMeanShellTensor o x j) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
    continuous_const.mul (supMean_shell_jet_spatial_continuous (o i) j)))

/-- Continuity of each tensor observation on the frozen shell sample carrier. -/
theorem supMean_shell_tensor_sample_continuous {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) (x : Vec 2) : Continuous (supMeanShellTensor o x) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
    continuous_const.mul (shellDerivativeEval_continuous (supMeanJetObservation (o i) x))))

/-- Pointwise integrability follows from the actual stored joint Gaussian law. -/
theorem supMean_shell_tensor_integrable (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) :
    Integrable (supMeanShellTensor o x) (ShellField.shellMarginalLaw M.P k).toMeasure := by
  apply memLp_one_iff_integrable.mp
  apply memLp_piLp_iff.mpr
  intro i
  exact (supMean_shell_jets_gaussian M h hM k).memLp (o i,x) 1 (by simp)

/-- The centered-increment MGF's tensor norm is exactly the actual field difference norm. -/
theorem supMean_shell_tensor_increment_norm {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) (x y : Vec 2) (j : ShellField 2) :
    supMeanTensorNorm (fun i z => supMeanShellJetScalar (o i) y z-supMeanShellJetScalar (o i) x z) j =
      ‖supMeanShellTensor o y j-supMeanShellTensor o x j‖ := by
  unfold supMeanTensorNorm
  congr 1

end
end ASDExplicitGamma.Gaussian
