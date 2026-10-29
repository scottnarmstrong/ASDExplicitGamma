module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandKernelTrace
public import ASDExplicitGamma.Gaussian.SupMeanShellPairKernel

/-! Static operator bounds for the full-band kernel, summing variances before roots. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Gaussian Model
open Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- Orthogonal shell coordinates give the exact static projection variance. -/
theorem upper_cell_band_static_projection_norm {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet) (a : ι → ℝ) (x : Vec 2) :
    ‖∑ z, a z • upperCellBandKernel M h k w (o z) x‖^2 =
      ∑ i, w i^2 * ‖∑ z, a z • supMeanShellJetKernel M h (k i) (o z) x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖(PiLp.projₗ (𝕜 := ℝ) (p := 2) (fun _ : Fin b => WhiteNoise) i)
    (∑ z, a z • upperCellBandKernel M h k w (o z) x)‖^2 = _
  rw [map_sum]
  simp only [map_smul, PiLp.projₗ_apply, upperCellBandKernel]
  simp_rw [smul_comm (a _) (w i), ← Finset.smul_sum]
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- Unit gradient projections retain the sharp ell_1 constant for the complete band. -/
theorem upper_cell_band_first_kernel_projection {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    (x : Vec 2) (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ ≤ 1) :
    ‖∑ i, v i • upperCellBandKernel M h k w (.first i) x‖ ≤
      Real.sqrt (waveEll1^2 * upperCellBandVariance M h k w 1) := by
  apply (Real.le_sqrt (norm_nonneg _)
    (mul_nonneg (sq_nonneg _) (upper_cell_band_variance_nonneg M h k w _))).mpr
  rw [upper_cell_band_static_projection_norm]
  calc
    _ ≤ ∑ i, w i^2 * (waveEll1^2 *
        ((supMeanShellKernelAmplitude M h (k i))^2 / ((3:ℝ)^(k i))^2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hh := pow_le_pow_left₀ (norm_nonneg _)
        (supMean_shell_first_kernel_projection M h (k i) x v hv) 2
      rwa [Real.sq_sqrt (by positivity)] at hh
    _ = _ := by
      simp only [supMean_shell_kernel_amplitude_sq, upperCellBandVariance,
        Finset.mul_sum, Nat.reduceMul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Unit Hessian projections retain ell_2, without replacing it by a trace constant. -/
theorem upper_cell_band_second_kernel_projection {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (k : Fin b → ℤ) (w : Fin b → ℝ)
    (x : Vec 2) (v : EuclideanSpace ℝ (Fin 2 × Fin 2)) (hv : ‖v‖ ≤ 1) :
    ‖∑ i, v i • upperCellBandKernel M h k w (.second i.1 i.2) x‖ ≤
      Real.sqrt (waveEll2^2 * upperCellBandVariance M h k w 2) := by
  apply (Real.le_sqrt (norm_nonneg _)
    (mul_nonneg (sq_nonneg _) (upper_cell_band_variance_nonneg M h k w _))).mpr
  rw [upper_cell_band_static_projection_norm]
  calc
    _ ≤ ∑ i, w i^2 * (waveEll2^2 *
        ((supMeanShellKernelAmplitude M h (k i))^2 / ((3:ℝ)^(k i))^4)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hh := pow_le_pow_left₀ (norm_nonneg _)
        (supMean_shell_second_kernel_projection M h (k i) x v hv) 2
      rwa [Real.sq_sqrt (by positivity)] at hh
    _ = _ := by
      simp only [supMean_shell_kernel_amplitude_sq, upperCellBandVariance,
        Finset.mul_sum, Nat.reduceMul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end
end ASDExplicitGamma.Scalar
