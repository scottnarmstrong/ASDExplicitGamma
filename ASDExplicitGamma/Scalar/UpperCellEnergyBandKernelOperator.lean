module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandKernelTrace
public import ASDExplicitGamma.Gaussian.SupMeanKernelProjectionIncrement

/-! Projected full-band kernel increments retain their sharp operator constants. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- Every tensor projection has an exact orthogonal sum over physical shells. -/
theorem upper_cell_band_kernel_projection_norm {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (a : ι → ℝ) (x y : Vec 2) :
    ‖∑ z,a z • (upperCellBandKernel M h k w (o z) y-
      upperCellBandKernel M h k w (o z) x)‖^2 =
      ∑ i,w i^2*‖∑ z,a z • (supMeanShellJetKernel M h (k i) (o z) y-
        supMeanShellJetKernel M h (k i) (o z) x)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(PiLp.projₗ (𝕜 := ℝ) (p := 2) (fun _ : Fin b => WhiteNoise) i) (∑ z,a z •
    (upperCellBandKernel M h k w (o z) y-upperCellBandKernel M h k w (o z) x))‖^2 = _
  rw [map_sum]
  simp only [map_smul,map_sub,PiLp.projₗ_apply,upperCellBandKernel]
  simp_rw [← smul_sub,smul_comm (a _) (w i),← Finset.smul_sum]
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

/-- Gradient projection increments use ell_2 and the SUM of second-order
shell variances. No dimension-dependent triangle estimate intervenes. -/
theorem upper_cell_band_first_projection_increment {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    (a : Fin 2 → ℝ) (x y : Vec 2) :
    ‖∑ z,a z • (upperCellBandKernel M h k w (.first z) y-
      upperCellBandKernel M h k w (.first z) x)‖^2 ≤
      (waveEll2^2*upperCellBandVariance M h k w 2)*(∑ z,a z^2)*
        ((y-x) 0^2+(y-x) 1^2) := by
  rw [upper_cell_band_kernel_projection_norm]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (supMean_kernel_first_projection_increment (supMeanShellKernelAmplitude M h (k i))
        (supMeanShellKernelLength (k i)) a x y) (sq_nonneg (w i)))
  change (∑ i,w i^2*‖∑ z,a z • (supMeanShellJetKernel M h (k i) (.first z) y-
    supMeanShellJetKernel M h (k i) (.first z) x)‖^2) ≤ _ at hh
  refine hh.trans_eq ?_
  simp only [supMean_shell_kernel_amplitude_sq,supMeanShellKernelLength,upperCellBandVariance,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  norm_num only [Nat.reduceMul]
  ring

/-- Hessian projection increments use ell_3 from the genuine third weak kernel. -/
theorem upper_cell_band_second_projection_increment {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    (a : Fin 2 × Fin 2 → ℝ) (x y : Vec 2) :
    ‖∑ z,a z • (upperCellBandKernel M h k w (.second z.1 z.2) y-
      upperCellBandKernel M h k w (.second z.1 z.2) x)‖^2 ≤
      (waveEll3^2*upperCellBandVariance M h k w 3)*(∑ z,a z^2)*
        ((y-x) 0^2+(y-x) 1^2) := by
  rw [upper_cell_band_kernel_projection_norm]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (supMean_kernel_second_projection_increment (supMeanShellKernelAmplitude M h (k i))
        (supMeanShellKernelLength (k i)) a x y) (sq_nonneg (w i)))
  change (∑ i,w i^2*‖∑ z,a z • (supMeanShellJetKernel M h (k i) (.second z.1 z.2) y-
    supMeanShellJetKernel M h (k i) (.second z.1 z.2) x)‖^2) ≤ _ at hh
  refine hh.trans_eq ?_
  simp only [supMean_shell_kernel_amplitude_sq,supMeanShellKernelLength,upperCellBandVariance,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro i _
  norm_num only [Nat.reduceMul]
  ring

end
end ASDExplicitGamma.Scalar
