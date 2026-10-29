module

public import ASDExplicitGamma.Scalar.OldHessianTrialIntegratedCovariance
public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenAlgebra

/-! Exact signed frozen affine covariance after genuine cell integration. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- A fixed matrix load pairs integrably with two genuine L2 coordinate families. -/
theorem old_hessian_matrix_pairing_integrable (U : TriadicCube 2)
    (z : Vec 2 → Vec 2) (T : Vec 2 → Mat 2)
    (hz : ∀ i,MemLp (fun x => z x i) 2 (normalizedCubeMeasure U))
    (hT : ∀ i j,MemLp (fun x => T x i j) 2 (normalizedCubeMeasure U)) (e : Vec 2) :
    Integrable (fun x => vecDot (z x) (matVecMul (T x) e)) (normalizedCubeMeasure U) := by
  simp only [vecDot,matVecMul,Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => by
    simpa only [Pi.mul_apply,mul_assoc] using ((hz i).integrable_mul (hT i j)).mul_const (e j)))

/-- The negative principal term and retained covariance error keep their
exact signs and coefficients under the physical cell integral. -/
theorem old_hessian_integrated_frozen_split (U : TriadicCube 2)
    (z : Fin 2 → Vec 2 → Vec 2) (T : Vec 2 → Mat 2) (E : Mat 2) (v lam : ℝ)
    (hz : ∀ i k,MemLp (fun x => z i x k) 2 (normalizedCubeMeasure U))
    (hT : ∀ i j,MemLp (fun x => T x i j) 2 (normalizedCubeMeasure U)) :
    2*lam*(∑ i : Fin 2,cubeAverage U (fun x => vecDot (matVecMul responsePlanarJ (z i x))
      (matVecMul (T x) (matVecMul ((v/2) • responsePlanarJ+E) (basisVec i)))) )=
      -lam*v*(∑ i : Fin 2,cubeAverage U (fun x => vecDot (z i x)
        (matVecMul responsePlanarJ (matVecMul (T x) (matVecMul responsePlanarJ (basisVec i))))))-
      2*lam*(∑ i : Fin 2,cubeAverage U (fun x => vecDot (z i x)
        (matVecMul responsePlanarJ (matVecMul (T x) (matVecMul E (basisVec i)))))) := by
  let μ := normalizedCubeMeasure U
  let JT := fun x => responsePlanarJ*(T x)
  have hJT (i j : Fin 2) : MemLp (fun x => JT x i j) 2 μ := by
    fin_cases i
    · simpa [JT,Matrix.mul_apply,Matrix.vecMul,dotProduct,responsePlanarJ,Fin.sum_univ_two,Pi.neg_def] using (hT 1 j).neg
    · simpa [JT,Matrix.mul_apply,Matrix.vecMul,dotProduct,responsePlanarJ,Fin.sum_univ_two,Pi.neg_def] using hT 0 j
  have hJz (i k : Fin 2) : MemLp (fun x => matVecMul responsePlanarJ (z i x) k) 2 μ := by
    fin_cases k
    · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,Pi.neg_def] using (hz i 1).neg
    · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two,Pi.neg_def] using hz i 0
  let f := fun i x => vecDot (matVecMul responsePlanarJ (z i x))
    (matVecMul (T x) (matVecMul ((v/2) • responsePlanarJ+E) (basisVec i)))
  let g := fun i x => vecDot (z i x)
    (matVecMul responsePlanarJ (matVecMul (T x) (matVecMul responsePlanarJ (basisVec i))))
  let q := fun i x => vecDot (z i x)
    (matVecMul responsePlanarJ (matVecMul (T x) (matVecMul E (basisVec i))))
  have hf (i : Fin 2) : Integrable (f i) μ :=
    old_hessian_matrix_pairing_integrable U _ T (hJz i) hT _
  have hmul (B C : Mat 2) (e : Vec 2) : matVecMul (B*C) e=matVecMul B (matVecMul C e) :=
    (Matrix.mulVec_mulVec e B C).symm
  have hg (i : Fin 2) : Integrable (g i) μ := by
    have hh := old_hessian_matrix_pairing_integrable U (z i) JT (hz i) hJT
      (matVecMul responsePlanarJ (basisVec i))
    simpa only [JT,hmul] using hh
  have hq (i : Fin 2) : Integrable (q i) μ := by
    have hh := old_hessian_matrix_pairing_integrable U (z i) JT (hz i) hJT (matVecMul E (basisVec i))
    simpa only [JT,hmul] using hh
  have hgs := integrable_finsetSum Finset.univ (fun i _ => hg i)
  have hqs := integrable_finsetSum Finset.univ (fun i _ => hq i)
  have he : (fun x => 2*lam*(∑ i : Fin 2,f i x))=
      (fun x => (-lam*v)*(∑ i : Fin 2,g i x)-(2*lam)*(∑ i : Fin 2,q i x)) := by
    funext x
    exact old_hessian_frozen_affine_split (fun i => z i x) (T x) E v lam
  have hi := congrArg (fun F : Vec 2 → ℝ => ∫ x,F x ∂μ) he
  rw [integral_sub (hgs.const_mul _) (hqs.const_mul _)] at hi
  simp only [integral_const_mul,integral_finsetSum _ (fun i _ => hf i),
    integral_finsetSum _ (fun i _ => hg i),integral_finsetSum _ (fun i _ => hq i)] at hi
  simpa only [cubeAverage_eq_integral_normalizedCubeMeasure] using hi

end
end ASDExplicitGamma.Scalar
