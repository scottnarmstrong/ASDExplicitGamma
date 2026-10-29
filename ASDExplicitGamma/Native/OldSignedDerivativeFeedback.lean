module

public import ASDExplicitGamma.Native.OldSignedDerivativeRowMembership
public import ASDExplicitGamma.Native.OldSignedVectorHaarPairing

/-! Joint constant-one local derivative feedback for distinct covariance
potentials and the actual reciprocal gradients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- AN (3.2) followed by exact vector duality controls every finite local
feedback family. Both the reciprocal gradients and the direction-dependent
first potentials stay in the same actual cell. -/
theorem old_signed_derivative_feedback_bound {I A : Type*} [Fintype A]
    (e : HilbertBasis I ℝ WhiteNoise) (s : Finset I) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (g : A → H1Function (openCubeSet Q)) (u : I → A → H10Function (openCubeSet Q)) :
    |∑ a : A,∑ k : Fin 2,pairing Q (fun x => (g a).grad x k)
      (fun x => oldSignedDerivativeRow e s b L Q (fun n => u n a) x k)|≤
      oldSignedDerivativeKappa (cubeScaleFactor Q) b L.1*
        Real.sqrt (∑ a : A,vectorWeakHaarNorm Q (g a).grad^2)*
        Real.sqrt (∑ a : A,∑ n : s,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2) := by
  let C := oldSignedDerivativeKappa (cubeScaleFactor Q) b L.1
  have hC : 0≤C := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' Q).le b L.1
  have hk a : 0≤vectorWeakHaarNorm Q (g a).grad := Real.sqrt_nonneg _
  have hsum a : 0≤∑ n : s,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hpair a := old_signed_vector_haar_pairing_bound Q (g a).grad
    (oldSignedDerivativeRow e s b L Q (fun n => u n a))
    (fun k => (g a).grad_memL2_normalizedCubeMeasure k)
    (old_signed_derivative_row_memLp e s b L Q (fun n => u n a))
    (old_signed_derivative_row_bound e s b L Q (fun n => u n a)).1
  have hb a := mul_le_mul_of_nonneg_left
    (old_signed_derivative_row_bound e s b L Q (fun n => u n a)).2 (hk a)
  have hcs := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun a : A => sq_nonneg (vectorWeakHaarNorm Q (g a).grad)) hsum
  simp_rw [Real.sqrt_sq (hk _)] at hcs
  calc
    _ ≤ ∑ a : A,|∑ k : Fin 2,pairing Q (fun x => (g a).grad x k)
        (fun x => oldSignedDerivativeRow e s b L Q (fun n => u n a) x k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : A,vectorWeakHaarNorm Q (g a).grad*
        (C*Real.sqrt (∑ n : s,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2)) :=
      Finset.sum_le_sum (fun a _ => (hpair a).trans (hb a))
    _ = C*(∑ a : A,vectorWeakHaarNorm Q (g a).grad*
        Real.sqrt (∑ n : s,vectorWeakHaarNorm Q (u n a).toH1Function.grad^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hcs hC).trans_eq (by ring)

end
end ASDExplicitGamma.Native
