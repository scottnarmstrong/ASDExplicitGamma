module

public import ASDExplicitGamma.Gaussian.WaveGateLocalTensor
public import ASDExplicitGamma.Gaussian.SupMeanDyadicInterior
public import ASDExplicitGamma.Gaussian.WaveGatePhysicalFunctional

/-! The exact physical Frobenius derivative size is measurable in its closed-square local information. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Provider.BadEvents MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Dense-center maxima are local to the literal closed square, even if its
boundary lies on the boundary of the surrounding observation region. -/
theorem wave_gate_tensor_mesh_local_measurable {U : Set (Vec 2)}
    (c : Vec 2) (s : ℝ) (hs : 0 < s) (hU : supMeanClosedSquare c s ⊆ U)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (n : ℕ) :
    @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j => supMeanDyadicMaximum c s (fun x => supMeanShellTensor o x j) n) := by
  let waveGateLocalInfo : MeasurableSpace (ShellField 2) := ShellField.lihLocalSigma U
  have hm (i : SupMeanDyadicIndex n) : Measurable (fun j => ‖supMeanShellTensor o (supMeanDyadicCenter c s n i) j‖) :=
    (wave_gate_tensor_local_measurable (by positivity : 0 < s/(2*(2:ℝ)^n))
      ((supMean_dyadic_center_ball_subset c s hs n i).trans hU) o).norm
  have hh := Finset.measurable_sup' (s := Finset.univ) Finset.univ_nonempty (fun i _ => hm i)
  convert hh using 1
  funext j
  exact (Finset.sup'_apply Finset.univ_nonempty
    (fun (i : SupMeanDyadicIndex n) (j : ShellField 2) => ‖supMeanShellTensor o (supMeanDyadicCenter c s n i) j‖) j).symm

/-- The actual full Frobenius supremum is local. Its countable-center limit
is the same compact norm proved in GA-SUP-MEAN, with no boundary extension. -/
theorem wave_gate_tensor_supremum_local_measurable {U : Set (Vec 2)}
    (c : Vec 2) (s : ℝ) (hs : 0 < s) (hU : supMeanClosedSquare c s ⊆ U)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) :
    @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) inferInstance
      (fun j => ‖supMeanShellSquareTensor o c s j‖) := by
  let waveGateLocalInfo : MeasurableSpace (ShellField 2) := ShellField.lihLocalSigma U
  apply measurable_of_tendsto_metrizable (fun n => wave_gate_tensor_mesh_local_measurable c s hs hU o n)
  apply tendsto_pi_nhds.mpr
  intro j
  exact supMean_dyadic_maximum_tendsto c s hs (fun x => supMeanShellTensor o x j)
    (supMean_shell_tensor_spatial_continuous o j)

/-- The exact source derivative threshold reads only the square's local shell
information, retaining the same scalar frame and both Frobenius norms. -/
theorem wave_gate_derivative_size_local_measurable {U : Set (Vec 2)}
    (c : Vec 2) (s σ : ℝ) (hs : 0 < s) (hU : supMeanClosedSquare c s ⊆ U) :
    @Measurable (ShellField 2) ℝ (ShellField.lihLocalSigma U) inferInstance (waveGateDerivativeSize c s σ) := by
  let waveGateLocalInfo : MeasurableSpace (ShellField 2) := ShellField.lihLocalSigma U
  exact ((wave_gate_tensor_supremum_local_measurable c s hs hU Q3SpatialJet.first).const_mul (s/σ)).add
    ((wave_gate_tensor_supremum_local_measurable c s hs hU
      (fun i : Fin 2 × Fin 2 => .second i.1 i.2)).const_mul (s^2/σ))

end
end ASDExplicitGamma.Gaussian
