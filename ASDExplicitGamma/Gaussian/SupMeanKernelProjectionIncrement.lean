module

public import ASDExplicitGamma.Gaussian.SupMeanHilbertProjectionIncrement
public import ASDExplicitGamma.Gaussian.SupMeanKernelTensorBounds
public import ASDExplicitGamma.Gaussian.SupMeanKernelThirdBound
public import ASDExplicitGamma.Gaussian.SupMeanKernelLineDerivative
public import ASDExplicitGamma.Gaussian.SupMeanTensorContraction

/-! Sharp covariance-operator spatial increments of the actual q3 tensor kernels. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
open scoped BigOperators RealInnerProductSpace
noncomputable section

/-- The first jet's spatial successors are exactly the two Hessian slots. -/
theorem supMean_kernel_first_successor_index (i d : Fin 2) :
    supMeanKernelJetSuccessor (.first i) d = supMeanKernelJetIndex (.second i d) := by
  fin_cases i <;> fin_cases d <;>
    norm_num [supMeanKernelJetSuccessor, supMeanKernelJetIndex, h3Next, Q3SpatialJet.count]

/-- Squared sharp CM bound, in the literal Hessian coordinate sum. -/
theorem supMean_kernel_second_cm_sq (β : ℝ) (L : {l : ℝ // 0 < l}) (u : WhiteNoise) (x : Vec 2) :
    (∑ i : Fin 2 × Fin 2, (Real.sqrt 2 *
      q3Convolution β L (supMeanKernelJetIndex (.second i.1 i.2)) u x)^2) ≤
        (waveEll2^2*(β^2/L.val^4))*‖u‖^2 := by
  have hb := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg u))).mpr (supMean_kernel_second_cm_norm β L u x)
  rw [EuclideanSpace.real_norm_sq_eq, mul_pow, Real.sq_sqrt (by positivity)] at hb
  exact hb

private theorem kernel_projection_increment_of_successors {ι : Type} [Fintype ι]
    (β : ℝ) (L : {l : ℝ // 0 < l}) (o : ι → Q3SpatialJet) (M : ℝ) (hM : 0 ≤ M)
    (hnext : ∀ u x, (∑ i, ∑ d : Fin 2,
      (Real.sqrt 2*q3Convolution β L (supMeanKernelJetSuccessor (o i) d) u x)^2) ≤ M*‖u‖^2)
    (a : ι → ℝ) (x y : Vec 2) :
    ‖∑ i, a i • (Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o i)) y-
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o i)) x)‖^2 ≤
        M*(∑ i, a i^2)*((y-x) 0^2+(y-x) 1^2) := by
  let v := y-x
  let K (i : ι) (t : ℝ) := Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o i)) (x+t • v)
  let D (i : ι) (t : ℝ) := v 0 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (o i) 0) (x+t • v))+
    v 1 • (Real.sqrt 2 • q3Section β L (supMeanKernelJetSuccessor (o i) 1) (x+t • v))
  have hB (u : WhiteNoise) (t : ℝ) : (∑ i, ⟪u,D i t⟫^2) ≤ (M*(v 0^2+v 1^2))*‖u‖^2 := by
    have hc := supMean_tensor_two_coordinate_contraction
      (fun (i : ι) d => Real.sqrt 2*q3Convolution β L (supMeanKernelJetSuccessor (o i) d) u (x+t • v)) v
    have hb := hc.trans (mul_le_mul_of_nonneg_left (hnext u (x+t • v)) (by positivity))
    calc
      _ = ∑ i, (v 0*(Real.sqrt 2*q3Convolution β L (supMeanKernelJetSuccessor (o i) 0) u (x+t • v))+
          v 1*(Real.sqrt 2*q3Convolution β L (supMeanKernelJetSuccessor (o i) 1) u (x+t • v)))^2 := by
        simp only [D, inner_add_right, real_inner_smul_right, q3Convolution]
      _ ≤ (v 0^2+v 1^2)*(M*‖u‖^2) := hb
      _ = _ := by ring
  have hh := supMean_hilbert_kernel_projection_increment K D (M*(v 0^2+v 1^2)) (by positivity)
    (fun i u t => supMean_kernel_line_hasDerivAt β L (o i) u x v t) hB a
  have h1 : x+(1:ℝ) • v = y := by dsimp only [v]; simp only [one_smul]; abel
  have hb : ‖∑ i, a i • (Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o i)) y-
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (o i)) x)‖^2 ≤
        (M*(v 0^2+v 1^2))*(∑ i, a i^2) := by
    simpa only [K, h1, zero_smul, add_zero] using! hh
  exact hb.trans_eq (by dsimp only [v]; ring)

/-- Every projected gradient kernel increment uses the sharp Hessian operator
constant ell_2, with its exact Euclidean spatial distance. -/
theorem supMean_kernel_first_projection_increment (β : ℝ) (L : {l : ℝ // 0 < l})
    (a : Fin 2 → ℝ) (x y : Vec 2) :
    ‖∑ i : Fin 2, a i • (Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) y-
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.first i)) x)‖^2 ≤
        (waveEll2^2*(β^2/L.val^4))*(∑ i, a i^2)*((y-x) 0^2+(y-x) 1^2) := by
  apply kernel_projection_increment_of_successors β L Q3SpatialJet.first _ (by positivity) _ a x y
  intro u z
  simpa only [supMean_kernel_first_successor_index, Fintype.sum_prod_type] using!
    supMean_kernel_second_cm_sq β L u z

/-- Every projected Hessian kernel increment uses ell_3 from the genuine third
weak tensor, without assuming third derivatives of the random shell. -/
theorem supMean_kernel_second_projection_increment (β : ℝ) (L : {l : ℝ // 0 < l})
    (a : Fin 2 × Fin 2 → ℝ) (x y : Vec 2) :
    ‖∑ i : Fin 2 × Fin 2, a i • (Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) y-
      Real.sqrt 2 • q3Section β L (supMeanKernelJetIndex (.second i.1 i.2)) x)‖^2 ≤
        (waveEll3^2*(β^2/L.val^6))*(∑ i, a i^2)*((y-x) 0^2+(y-x) 1^2) := by
  apply kernel_projection_increment_of_successors β L (fun i : Fin 2 × Fin 2 => .second i.1 i.2)
    _ (by positivity) _ a x y
  intro u z
  simpa only [Fintype.sum_prod_type] using! supMean_kernel_third_cm_sq β L u z

end
end ASDExplicitGamma.Gaussian
