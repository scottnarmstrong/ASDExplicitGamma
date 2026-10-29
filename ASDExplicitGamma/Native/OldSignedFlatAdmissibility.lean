module

public import ASDExplicitGamma.Scalar.TopSourceResidual
public import ASDExplicitGamma.Main.FlatFieldH1Bounds

/-! The actual H1 flat fields supply positive-Haar series convergence.
These discharge regularity inputs of the internal flat-source estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Main ASDExplicitGamma.Gaussian
noncomputable section

/-- Every pair of actual H1 coordinates is admissible for the positive
source projection bounds. Summability is proved, not hidden in a real tsum. -/
theorem old_signed_h1_vector_positive_admissible (Q : TriadicCube 2)
    (u : Fin 2 → H1Function (openCubeSet Q)) :
    ScalarPositiveHaarAdmissible Q (fun x i => u i x) := by
  refine ⟨?_,?_⟩
  · apply MemLp.of_eval
    intro i
    exact (u i).memL2_normalizedCubeMeasure
  · intro i
    have hs := positiveHaarIncrementSeries_summable Q (u i).memL2_normalizedCubeMeasure
      (u i).grad_memL2_normalizedCubeMeasure (u i).hasWeakGradient
    have hq : sourceHaarBase≤Real.sqrt 3 := by
      rw [sourceHaarBase,Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    apply hs.of_nonneg_of_le
      (fun j => mul_nonneg (pow_nonneg (le_trans zero_le_one source_haar_base_gt_one.le) _) (energy_nonneg Q _))
    intro j
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_trans zero_le_one source_haar_base_gt_one.le) hq _) (energy_nonneg Q _)

/-- Arbitrary affine centering and a fixed sign preserve genuine H1
regularity, hence the exact weighted positive-Haar increment summability. -/
theorem old_signed_centered_h1_vector_positive_admissible (Q : TriadicCube 2)
    (u : Fin 2 → H1Function (openCubeSet Q)) (c : Vec 2) (t : ℝ) :
    ScalarPositiveHaarAdmissible Q (fun x i => t*u i x-c i) := by
  let v (i : Fin 2) : H1Function (openCubeSet Q) := t • u i-
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => c i))
  have hv := old_signed_h1_vector_positive_admissible Q v
  have he : (fun x i => v i x)=(fun x i => t*u i x-c i) := by
    funext x i
    simp only [v,H1Function.sub_toFun,H1Function.smul_toFun]
    rfl
  rw [he] at hv
  exact hv

/-- The stronger order-one-quarter positive-Haar series used by the
recorded vector norms also converges for the actual H1 coordinates. -/
theorem old_signed_h1_vector_positive_summable (Q : TriadicCube 2)
    (u : Fin 2 → H1Function (openCubeSet Q)) (i : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => u i x))) :=
  positiveHaarIncrementSeries_summable Q (u i).memL2_normalizedCubeMeasure
    (u i).grad_memL2_normalizedCubeMeasure (u i).hasWeakGradient

/-- Centered actual H1 coordinates have the stronger recorded summability,
including either sign of the physical flat fields. -/
theorem old_signed_centered_h1_vector_positive_summable (Q : TriadicCube 2)
    (u : Fin 2 → H1Function (openCubeSet Q)) (c : Vec 2) (t : ℝ) (i : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => t*u i x-c i))) := by
  let v (i : Fin 2) : H1Function (openCubeSet Q) := t • u i-
    H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
      (contDiff_const : ContDiff ℝ 1 (fun _ : Vec 2 => c i))
  have hv := old_signed_h1_vector_positive_summable Q v i
  have he : (fun x => v i x)=(fun x => t*u i x-c i) := by
    funext x
    simp only [v,H1Function.sub_toFun,H1Function.smul_toFun]
    rfl
  simpa only [he] using hv

end
end ASDExplicitGamma.Native
