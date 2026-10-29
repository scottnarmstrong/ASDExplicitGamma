module

public import ASDExplicitGamma.Gaussian.SupMeanKernelCovariance
public import ASDExplicitGamma.Gaussian.SupMeanHilbertTensor
public import ASDExplicitGamma.Gaussian.WaveGateConstants

/-! Sharp pointwise Cameron-Martin tensor bounds for the genuine q3 convolution factor. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The full planar skew Frobenius payment is exactly two in the Hilbert Gram rows. -/
theorem supMean_kernel_skew_jet_covariance (β : ℝ) (L : {l : ℝ // 0 < l})
    (o p : Q3SpatialJet) (x y : Vec 2) :
    ⟪Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex o) x,
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex p) y⟫ =
        2*q3ScaledJetCovariance (β^2) L.val o p x y := by
  rw [real_inner_smul_left, real_inner_smul_right, supMean_kernel_jet_covariance]
  calc
    _ = (Real.sqrt 2)^2 * q3ScaledJetCovariance (β^2) L.val o p x y := by ring
    _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- Finite tensor combinations retain that exact covariance quadratic form. -/
theorem supMean_kernel_skew_gram_quadratic {ι : Type*} [Fintype ι]
    (β : ℝ) (L : {l : ℝ // 0 < l}) (o : ι → Q3SpatialJet) (x : Vec 2) (a : ι → ℝ) :
    (∑ i, ∑ j, a i*a j*⟪Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o i)) x,
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o j)) x⟫) =
        2*∑ i, ∑ j, a i*a j*q3ScaledJetCovariance (β^2) L.val (o i) (o j) x x := by
  simp_rw [supMean_kernel_skew_jet_covariance]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The true white-noise Cameron-Martin gradient tensor has the sharp ell_1 bound. -/
theorem supMean_kernel_first_cm_norm (β : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (x : Vec 2) :
    ‖(WithLp.toLp 2 (fun i : Fin 2 => Real.sqrt 2 *
      q3Convolution β L (supMeanKernelJetIndex (.first i)) u x) : EuclideanSpace ℝ (Fin 2))‖ ≤
        Real.sqrt (waveEll1^2*(β^2/L.val^2))*‖u‖ := by
  have hell : waveEll1^2 = 2*(78/5:ℝ) := by
    unfold waveEll1 waveR1
    exact Real.sq_sqrt (by norm_num)
  have hM : 0 ≤ waveEll1^2*(β^2/L.val^2) := by positivity
  have hg (a : Fin 2 → ℝ) :
      (∑ i, ∑ j, a i*a j*⟪Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) x,
        Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first j)) x⟫) ≤
          (waveEll1^2*(β^2/L.val^2))*(∑ i, a i^2) := by
    rw [supMean_kernel_skew_gram_quadratic, q3ScaledJetCovariance_first_quadratic, hell]
    exact le_of_eq (by ring)
  have hh := supMean_hilbert_tensor_norm_bound
    (fun i : Fin 2 => Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) x)
    _ hM hg u
  simpa only [real_inner_smul_right, q3Convolution] using! hh

/-- The true white-noise Hessian tensor uses ell_2, without replacing it by sqrt(tau_2). -/
theorem supMean_kernel_second_cm_norm (β : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (x : Vec 2) :
    ‖(WithLp.toLp 2 (fun i : Fin 2 × Fin 2 => Real.sqrt 2 *
      q3Convolution β L (supMeanKernelJetIndex (.second i.1 i.2)) u x) :
        EuclideanSpace ℝ (Fin 2 × Fin 2))‖ ≤
          Real.sqrt (waveEll2^2*(β^2/L.val^4))*‖u‖ := by
  have hell : waveEll2^2 = 2*((3432/5:ℝ)+(78/5:ℝ)^2) := by
    unfold waveEll2 waveR2 waveR1
    exact Real.sq_sqrt (by norm_num)
  have hM : 0 ≤ waveEll2^2*(β^2/L.val^4) := by positivity
  have hg (a : Fin 2 × Fin 2 → ℝ) :
      (∑ i, ∑ j, a i*a j*⟪Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) x,
        Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second j.1 j.2)) x⟫) ≤
          (waveEll2^2*(β^2/L.val^4))*(∑ i, a i^2) := by
    rw [supMean_kernel_skew_gram_quadratic, hell]
    have hb := mul_le_mul_of_nonneg_left
      (q3ScaledJetCovariance_second_quadratic_le (sq_nonneg β) L.val x a) (by norm_num : (0:ℝ) ≤ 2)
    convert hb using 1
    ring
  have hh := supMean_hilbert_tensor_norm_bound
    (fun i : Fin 2 × Fin 2 => Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) x)
    _ hM hg u
  simpa only [real_inner_smul_right, q3Convolution] using! hh

end
end ASDExplicitGamma.Gaussian
