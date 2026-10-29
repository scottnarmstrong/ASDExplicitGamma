module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandTensor
public import ASDExplicitGamma.Gaussian.SupMeanKernelDifferenceMoment

/-! A finite Hilbert direct sum realizes the full band covariance exactly. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The full band kernel in the Hilbert direct sum of the physical shell
white-noise spaces. Each shell retains its own amplitude and length. -/
def upperCellBandKernel {b : ℕ} (M : ABKModel 2) (h : ℝ)
    (k : Fin b → ℤ) (w : Fin b → ℝ) (o : Q3SpatialJet) (x : Vec 2) :
    PiLp 2 (fun _ : Fin b => WhiteNoise) :=
  WithLp.toLp 2 (fun i => w i • supMeanShellJetKernel M h (k i) o x)

/-- Scalar coordinates of the actual full-band tensor. -/
def upperCellBandJetScalar {b : ℕ} (k : Fin b → ℤ) (w : Fin b → ℝ)
    (o : Q3SpatialJet) (x : Vec 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt 2*upperCellBandJet k w (supMeanJetObservation o x) ω

/-- The full cross-point jet family has the genuine joint Gaussian law. -/
theorem upper_cell_band_scaled_jets_gaussian {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (fun p : Q3SpatialJet × Vec 2 => upperCellBandJetScalar k w p.1 p.2) := by
  have hh := (upper_cell_band_jets_gaussian M h hM k hk w).finite_linear_image
    (fun p : Q3SpatialJet × Vec 2 => fun _ : Fin 1 => supMeanJetObservation p.1 p.2)
    (fun (_ : Q3SpatialJet × Vec 2) (_ : Fin 1) => Real.sqrt 2)
  change IsCenteredGaussianFamily _ (fun (p : Q3SpatialJet × Vec 2) ω =>
    Real.sqrt 2*upperCellBandJet k w (supMeanJetObservation p.1 p.2) ω)
  simpa only [Fin.sum_univ_one] using hh

/-- Exact identification of every mixed full-band covariance with the
finite direct-sum kernel inner product. -/
theorem upper_cell_band_kernel_covariance {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (o p : Q3SpatialJet) (x y : Vec 2) :
    (∫ ω,upperCellBandJetScalar k w o x ω*upperCellBandJetScalar k w p y ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ⟪upperCellBandKernel M h k w o x,upperCellBandKernel M h k w p y⟫ := by
  have hscale (a b : ℝ) : (Real.sqrt 2*a)*(Real.sqrt 2*b) = 2*(a*b) := by
    calc
      _ = (Real.sqrt 2)^2*(a*b) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  simp only [upperCellBandJetScalar,hscale,integral_const_mul,
    upper_cell_band_jet_covariance M h hM k hk w,Finset.mul_sum,
    upperCellBandKernel,PiLp.inner_apply,
    real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  have hc := supMean_shell_jet_kernel_covariance M h hM (k i) o p x y
  simp only [supMeanShellJetScalar,hscale,integral_const_mul,
    q3Shell_stored_derivative_covariance M h hM] at hc
  rw [← hc]
  ring

/-- The actual band increment second moment equals the kernel Hilbert
distance, so the existing weak-kernel increment bounds apply to the full band. -/
theorem upper_cell_band_jet_difference_sq {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (o : Q3SpatialJet) (x y : Vec 2) :
    (∫ ω,(upperCellBandJetScalar k w o y ω-upperCellBandJetScalar k w o x ω)^2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ‖upperCellBandKernel M h k w o y-upperCellBandKernel M h k w o x‖^2 :=
  supMean_gaussian_kernel_difference_sq _ _
    (upper_cell_band_scaled_jets_gaussian M h hM k hk w)
    (fun p => upperCellBandKernel M h k w p.1 p.2)
    (fun p q => upper_cell_band_kernel_covariance M h hM k hk w p.1 q.1 p.2 q.2)
    (o,y) (o,x)

end
end ASDExplicitGamma.Scalar
