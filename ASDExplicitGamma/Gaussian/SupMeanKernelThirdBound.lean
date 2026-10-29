module

public import ASDExplicitGamma.Gaussian.SupMeanKernelSuccessor
public import ASDExplicitGamma.Gaussian.SupMeanHilbertTensor

/-! The source third weak tensor operator bound follows from its exact trace. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The complete third weak tensor has exactly tau_3 as its Frobenius trace. -/
theorem supMean_kernel_third_trace (β : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ p : (Fin 2 × Fin 2) × Fin 2, ‖Real.sqrt 2 • q3Section β L
      (supMeanKernelJetSuccessor (.second p.1.1 p.1.2) p.2) x‖^2) = waveTau3*(β^2/L.val^6) := by
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [supMean_kernel_second_successor_trace, Fin.sum_univ_two]
  ring

/-- The exact source ell_3 is the square root of that third-tensor trace. -/
theorem supMean_waveEll3_sq : waveEll3^2 = waveTau3 := by
  unfold waveEll3 waveTau3
  exact Real.sq_sqrt (by norm_num [waveMu3, waveR1, waveR2, waveR3])

/-- The third weak convolution tensor has the source ell_3 operator bound for
every actual white-noise Cameron-Martin direction. -/
theorem supMean_kernel_third_cm_sq (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) (x : Vec 2) :
    (∑ p : (Fin 2 × Fin 2) × Fin 2, (Real.sqrt 2 * q3Convolution β L
      (supMeanKernelJetSuccessor (.second p.1.1 p.1.2) p.2) u x)^2) ≤
        (waveEll3^2*(β^2/L.val^6))*‖u‖^2 := by
  have hh := supMean_hilbert_tensor_trace_sq_bound
    (fun p : (Fin 2 × Fin 2) × Fin 2 => Real.sqrt 2 • q3Section β L
      (supMeanKernelJetSuccessor (.second p.1.1 p.1.2) p.2) x) u
  rw [supMean_kernel_third_trace] at hh
  rw [supMean_waveEll3_sq]
  simpa only [real_inner_smul_right, q3Convolution] using! hh

end
end ASDExplicitGamma.Gaussian
