module

public import ASDExplicitGamma.Gaussian.SupMeanShellTensorFields
public import Algsuperdiff.Section3.Provider.BadEvents.SupMeasurability

/-! Reuse the stored-derivative locality API for the exact full q3 tensors. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Provider.BadEvents MeasureTheory
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Every actual stored scalar jet at an interior point reads only the
integral-local shell information; the third derivative is never requested. -/
theorem wave_gate_jet_scalar_local_measurable {U : Set (Vec 2)} {x : Vec 2} {r : ℝ}
    (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) (o : Q3SpatialJet) :
    @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) inferInstance (supMeanShellJetScalar o x) := by
  let waveGateLocalInfo : MeasurableSpace (ShellField 2) := ShellField.lihLocalSigma U
  cases o with
  | value =>
    change @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) _
      (fun j => Real.sqrt 2*(j x) 1 0)
    exact measurable_const.mul (measurable_entry_eval_lihLocalSigma hr hrU 1 0)
  | first i =>
    change @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) _
      (fun j => Real.sqrt 2*shellScalarEntry (j.deriv x (basisVec i)))
    exact measurable_const.mul (shellScalarEntry.continuous.measurable.comp
      (measurable_eval_deriv_apply_lihLocalSigma hr hrU (basisVec i)))
  | second i k =>
    change @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) _
      (fun j => Real.sqrt 2*shellScalarEntry (j.secondDeriv x (basisVec k) (basisVec i)))
    exact measurable_const.mul (shellScalarEntry.continuous.measurable.comp
      (measurable_eval_secondDeriv_apply_apply_lihLocalSigma hr hrU (basisVec k) (basisVec i)))

/-- All coordinates of the literal finite tensor retain the same local
information, including every stored Hessian entry and the skew factor sqrt(2). -/
theorem wave_gate_tensor_local_measurable {U : Set (Vec 2)} {x : Vec 2} {r : ℝ}
    (hr : 0 < r) (hrU : Metric.closedBall x r ⊆ U) {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) :
    @Measurable (ShellField 2) (EuclideanSpace ℝ ι) (ShellField.lihLocalSigma U) inferInstance
      (supMeanShellTensor o x) := by
  let waveGateLocalInfo : MeasurableSpace (ShellField 2) := ShellField.lihLocalSigma U
  exact (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval (fun i =>
    wave_gate_jet_scalar_local_measurable hr hrU (o i)))

end
end ASDExplicitGamma.Gaussian
