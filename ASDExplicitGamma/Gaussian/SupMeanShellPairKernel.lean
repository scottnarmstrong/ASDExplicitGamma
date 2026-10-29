module

public import ASDExplicitGamma.Gaussian.SupMeanShellPairObservation
public import ASDExplicitGamma.Gaussian.SupMeanKernelProjection
public import ASDExplicitGamma.Gaussian.SupMeanGaussianKernelVariance

/-! The actual combined compact observations retain the sum of sharp CM constants. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- A fixed unit gradient direction retains ell_1 under the actual shell kernel. -/
theorem supMean_shell_first_kernel_projection (M : ABKModel 2) (h : ℝ) (k : ℤ)
    (x : Vec 2) (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ ≤ 1) :
    ‖∑ i, v i • supMeanShellJetKernel M h k (.first i) x‖ ≤
      Real.sqrt (waveEll1^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^2)) := by
  apply supMean_kernel_projection_norm_le _ _ (Real.sqrt_nonneg _) _ v hv
  intro u
  simpa only [supMeanShellJetKernel, real_inner_smul_right, supMeanShellKernelLength,
    q3Convolution] using!
    supMean_kernel_first_cm_norm (supMeanShellKernelAmplitude M h k) (supMeanShellKernelLength k) u x

/-- A fixed unit Hessian direction retains ell_2, without a trace bound. -/
theorem supMean_shell_second_kernel_projection (M : ABKModel 2) (h : ℝ) (k : ℤ)
    (x : Vec 2) (v : EuclideanSpace ℝ (Fin 2 × Fin 2)) (hv : ‖v‖ ≤ 1) :
    ‖∑ i, v i • supMeanShellJetKernel M h k (.second i.1 i.2) x‖ ≤
      Real.sqrt (waveEll2^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^4)) := by
  apply supMean_kernel_projection_norm_le _ _ (Real.sqrt_nonneg _) _ v hv
  intro u
  simpa only [supMeanShellJetKernel, real_inner_smul_right, supMeanShellKernelLength,
    q3Convolution] using!
    supMean_kernel_second_cm_norm (supMeanShellKernelAmplitude M h k) (supMeanShellKernelLength k) u x

section
variable (c : Vec 2) (s : ℝ) [Nonempty (supMeanClosedSquare c s)]

/-- The exact sum of the two physical CM constants bounds every combined
countable observation; neither independence nor a common location is required. -/
theorem supMean_shell_pair_kernel_norm (M : ABKModel 2) (h : ℝ) (k : ℤ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ‖∑ i, supMeanShellPairCoefficient a b n i •
      supMeanShellJetKernel M h k (supMeanShellPairPoint c s n i).1
        (supMeanShellPairPoint c s n i).2‖ ≤
      a*Real.sqrt (waveEll1^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^2))+
      b*Real.sqrt (waveEll2^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^4)) := by
  simp only [Fintype.sum_sum_type, supMeanShellPairPoint, supMeanShellPairCoefficient,
    mul_smul, ← Finset.smul_sum]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (supMean_shell_first_kernel_projection M h k _ _
      (supMean_norming_vector_norm_le _ _)) ha)
    (mul_le_mul_of_nonneg_left (supMean_shell_second_kernel_projection M h k _ _
      (supMean_norming_vector_norm_le _ _)) hb)

/-- All actual variances are bounded by the squared combined physical CM
constant, with the Gaussian law and kernel covariance instantiated internally. -/
theorem supMean_shell_pair_projection_variance (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    Var[(fun j => supMeanCompactPairProjection (supMeanShellSquareTensor Q3SpatialJet.first c s j)
      (supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j) a b n);
        (ShellField.shellMarginalLaw M.P k).toMeasure] ≤
      (a*Real.sqrt (waveEll1^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^2))+
      b*Real.sqrt (waveEll2^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^4)))^2 := by
  simp_rw [supMean_shell_pair_observation_eq]
  rw [supMean_gaussian_kernel_combination_variance _ _
    ((supMean_shell_jets_gaussian M h hM k).comp (supMeanShellPairPoint c s n))
    (fun i => supMeanShellJetKernel M h k (supMeanShellPairPoint c s n i).1
      (supMeanShellPairPoint c s n i).2)
    (fun i j => supMean_shell_jet_kernel_covariance M h hM k _ _ _ _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (supMean_shell_pair_kernel_norm c s M h k a b ha hb n) 2

end
end
end ASDExplicitGamma.Gaussian
