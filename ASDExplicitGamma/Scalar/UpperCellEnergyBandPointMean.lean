module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandFields
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandKernelTrace
public import ASDExplicitGamma.Gaussian.SupMeanFirstMoments
public import ASDExplicitGamma.Gaussian.SupMeanSecondMoments

/-! Sharp base-point covariance traces for full-band Gaussian chaining. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

/-- The actual full-band first-tensor base mean uses tau_1 and the sum
of physical order-1 variances, with no shellwise triangle loss. -/
theorem upper_cell_band_first_tensor_mean {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) (x : Vec 2) :
    (∫ ω,‖upperCellBandTensor k w Q3SpatialJet.first x ω‖ ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt (waveTau1*upperCellBandVariance M h k w 1) := by
  have htrace (j : Fin b) :
      (∑ i : Fin 2,2*q3ShellDerivativeCovariance M h (k j) (.first x (basisVec i)) (.first x (basisVec i))) =
        waveTau1*(h^2*(3:ℝ)^(2*M.gamma*(k j:ℝ)))/((3:ℝ)^(k j))^2 := by
    have hh := supMean_shell_first_tensor_trace M h hM (k j) x
    simp only [supMeanShellFirstCoordinates,mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2),integral_const_mul] at hh
    simp_rw [pow_two,q3Shell_stored_derivative_covariance M h hM] at hh
    exact hh.trans (by simp only [div_eq_mul_inv]; ring)
  have hh := upper_cell_band_tensor_mean M h hM k hk w Q3SpatialJet.first x
  simp only [supMeanJetObservation,htrace] at hh
  refine hh.trans_eq ?_
  congr 1
  simp only [upperCellBandVariance,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  norm_num only [Nat.reduceMul]
  ring

/-- The actual full-band second-tensor base mean uses tau_2 and the sum
of physical order-2 variances, with no shellwise triangle loss. -/
theorem upper_cell_band_second_tensor_mean {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ) (x : Vec 2) :
    (∫ ω,‖upperCellBandTensor k w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) x ω‖ ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.sqrt (waveTau2*upperCellBandVariance M h k w 2) := by
  have htrace (j : Fin b) :
      (∑ i : Fin 2 × Fin 2,2*q3ShellDerivativeCovariance M h (k j) (.second x (basisVec i.1) (basisVec i.2)) (.second x (basisVec i.1) (basisVec i.2))) =
        waveTau2*(h^2*(3:ℝ)^(2*M.gamma*(k j:ℝ)))/((3:ℝ)^(k j))^4 := by
    have hh := supMean_shell_second_tensor_trace M h hM (k j) x
    simp only [supMeanShellSecondCoordinates,mul_pow,
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2),integral_const_mul] at hh
    simp_rw [pow_two,q3Shell_stored_derivative_covariance M h hM] at hh
    exact hh.trans (by simp only [div_eq_mul_inv]; ring)
  have hh := upper_cell_band_tensor_mean M h hM k hk w (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) x
  simp only [supMeanJetObservation,htrace] at hh
  refine hh.trans_eq ?_
  congr 1
  simp only [upperCellBandVariance,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  norm_num only [Nat.reduceMul]
  ring

end
end ASDExplicitGamma.Scalar
