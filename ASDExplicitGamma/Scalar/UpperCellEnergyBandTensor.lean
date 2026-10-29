module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandCovariance
public import ASDExplicitGamma.Gaussian.SupMeanShellTensorFields
public import ASDExplicitGamma.Gaussian.SupMeanGaussianMoments

/-! Actual full-band tensors with their planar skew Frobenius factor. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators ENNReal
noncomputable section

/-- The actual weighted-band derivative tensor, including sqrt(2) for the
full planar skew matrix norm. -/
def upperCellBandTensor {b : ℕ} (k : Fin b → ℤ) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2)
    (ω : Cutoff.CutoffSample 2) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt 2*upperCellBandJet k w (supMeanJetObservation (o i) x) ω)

/-- The actual tensor coordinates are jointly centered Gaussian. -/
theorem upper_cell_band_tensor_coordinates_gaussian {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (fun i ω => Real.sqrt 2*upperCellBandJet k w (supMeanJetObservation (o i) x) ω) := by
  have hh := (upper_cell_band_jets_gaussian M h hM k hk w).finite_linear_image
    (fun i (_ : Fin 1) => supMeanJetObservation (o i) x)
    (fun (_ : ι) (_ : Fin 1) => Real.sqrt 2)
  simpa only [Fin.sum_univ_one] using hh

/-- The squared full-band tensor norm has the SUM of actual weighted shell
covariance traces, rather than the square of a sum of shell norms. -/
theorem upper_cell_band_tensor_second_moment {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) :
    MemLp (fun ω => ‖upperCellBandTensor k w o x ω‖) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,‖upperCellBandTensor k w o x ω‖^2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∑ j,w j^2*∑ i,2*q3ShellDerivativeCovariance M h (k j)
        (supMeanJetObservation (o i) x) (supMeanJetObservation (o i) x) := by
  have hh := supMean_gaussian_tensor_moment (Cutoff.cutoffSampleLaw M).toMeasure _
    (upper_cell_band_tensor_coordinates_gaussian M h hM k hk w o x)
  refine ⟨hh.1,hh.2.trans ?_⟩
  simp only [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),integral_const_mul]
  simp_rw [pow_two,upper_cell_band_jet_covariance M h hM k hk w,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The base point of the full-band chaining estimate is paid by the square
root of the summed covariance trace. -/
theorem upper_cell_band_tensor_mean {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (x : Vec 2) :
    (∫ ω,‖upperCellBandTensor k w o x ω‖ ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt (∑ j,w j^2*∑ i,2*q3ShellDerivativeCovariance M h (k j)
        (supMeanJetObservation (o i) x) (supMeanJetObservation (o i) x)) := by
  have hh := upper_cell_band_tensor_second_moment M h hM k hk w o x
  have hv := ProbabilityTheory.variance_nonneg
    (fun ω => ‖upperCellBandTensor k w o x ω‖) (Cutoff.cutoffSampleLaw M).toMeasure
  rw [ProbabilityTheory.variance_eq_sub hh.1] at hv
  simp only [Pi.pow_apply] at hv
  rw [hh.2] at hv
  exact Real.le_sqrt_of_sq_le (by linarith only [hv])

end
end ASDExplicitGamma.Scalar
