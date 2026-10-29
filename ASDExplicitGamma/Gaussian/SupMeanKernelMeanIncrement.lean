module

public import ASDExplicitGamma.Gaussian.SupMeanKernelDirectionalTrace
public import ASDExplicitGamma.Gaussian.SupMeanKernelLineDerivative

/-! Exact mean-square spatial increment constants for the actual q3 kernel tensors. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- First-tensor kernel increments retain the directional half-trace tau_2/2. -/
theorem supMean_kernel_first_increment_trace (β : ℝ) (L : {l : ℝ // 0 < l}) (x y : Vec 2) :
    (∑ i : Fin 2, ‖Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) y-
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) x‖^2) ≤
        (waveTau2/2)*(β^2/L.val^4)*((y-x) 0^2+(y-x) 1^2) := by
  let v := y-x
  let C := Real.sqrt ((waveTau2/2)*(β^2/L.val^4)*(v 0^2+v 1^2))
  have htau : 0 ≤ waveTau2 := by norm_num [waveTau2, waveMu2, waveR1, waveR2]
  have hCsq : C^2 = (waveTau2/2)*(β^2/L.val^4)*(v 0^2+v 1^2) := Real.sq_sqrt (by positivity)
  have hh := supMean_hilbert_tensor_increment_sq
    (fun (i : Fin 2) t => Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) (x+t • v))
    (fun (i : Fin 2) t => v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.first i) 0) (x+t • v))+
      v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.first i) 1) (x+t • v)))
    C (Real.sqrt_nonneg _) (fun i u t => supMean_kernel_line_hasDerivAt β L (.first i) u x v t)
    (fun t => by rw [supMean_kernel_first_directional_trace, hCsq])
  rw [hCsq] at hh
  have h1 : x+(1:ℝ) • v = y := by dsimp only [v]; simp only [one_smul]; abel
  simpa only [h1, zero_smul, add_zero, v] using! hh

/-- Hessian kernel increments use tau_3/2, obtained from the genuine third weak
kernel, with no random C3-shell assumption. -/
theorem supMean_kernel_second_increment_trace (β : ℝ) (L : {l : ℝ // 0 < l}) (x y : Vec 2) :
    (∑ i : Fin 2 × Fin 2,
      ‖Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) y-
        Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) x‖^2) ≤
          (waveTau3/2)*(β^2/L.val^6)*((y-x) 0^2+(y-x) 1^2) := by
  let v := y-x
  let C := Real.sqrt ((waveTau3/2)*(β^2/L.val^6)*(v 0^2+v 1^2))
  have htau : 0 ≤ waveTau3 := by norm_num [waveTau3, waveMu3, waveR1, waveR2, waveR3]
  have hCsq : C^2 = (waveTau3/2)*(β^2/L.val^6)*(v 0^2+v 1^2) := Real.sq_sqrt (by positivity)
  have hh := supMean_hilbert_tensor_increment_sq
    (fun (i : Fin 2 × Fin 2) t => Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) (x+t • v))
    (fun (i : Fin 2 × Fin 2) t => v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.second i.1 i.2) 0) (x+t • v))+
      v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (.second i.1 i.2) 1) (x+t • v)))
    C (Real.sqrt_nonneg _) (fun i u t => supMean_kernel_line_hasDerivAt β L (.second i.1 i.2) u x v t)
    (fun t => by rw [supMean_kernel_second_directional_trace, hCsq])
  rw [hCsq] at hh
  have h1 : x+(1:ℝ) • v = y := by dsimp only [v]; simp only [one_smul]; abel
  simpa only [h1, zero_smul, add_zero, v] using! hh

end
end ASDExplicitGamma.Gaussian
