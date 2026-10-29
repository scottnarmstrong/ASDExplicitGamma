module

public import ASDExplicitGamma.Scalar.OldHessianTrialMeanCovariancePairing
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! The complete frozen covariance contracts after physical cell integration. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Finite matrix action inside the true cell integral. All product
integrability is derived from the two actual L2 coordinate families. -/
theorem old_hessian_averaged_matrix_pairing (U : TriadicCube 2)
    (w : Vec 2 → Vec 2) (T : Vec 2 → Mat 2)
    (hw : ∀ i,MemLp (fun x => w x i) 2 (normalizedCubeMeasure U))
    (hT : ∀ i l,MemLp (fun x => T x i l) 2 (normalizedCubeMeasure U)) (a : ℝ) (m : Vec 2) :
    cubeAverage U (fun x => vecDot (a • w x) (matVecMul (T x) m))=
      ∑ l : Fin 2,(a*m l)*cubeAverage U (fun x => vecDot (w x) (matVecMul (T x) (basisVec l))) := by
  have hi (l : Fin 2) : Integrable (fun x => vecDot (w x) (matVecMul (T x) (basisVec l)))
      (normalizedCubeMeasure U) := by
    simp_rw [old_hessian_matrix_basis_column]
    exact integrable_finsetSum _ (fun i _ => (hw i).integrable_mul (hT i l))
  have he : (fun x => vecDot (a • w x) (matVecMul (T x) m))=
      (fun x => ∑ l : Fin 2,(a*m l)*vecDot (w x) (matVecMul (T x) (basisVec l))) := by
    funext x
    simp_rw [old_hessian_matrix_basis_column]
    simp only [vecDot,matVecMul,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_finsetSum _ (fun l _ => (hi l).const_mul (a*m l))]
  simp only [integral_const_mul,←cubeAverage_eq_integral_normalizedCubeMeasure]

/-- The exact original complete-mode mean covariance contracts through
actual spatially varying source and TOP matrices. The finite parent and
source-cell labels stay independent. -/
theorem old_hessian_integrated_mean_covariance_hasSum (Q : TriadicCube 2) (fine : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q fine)
    (w : Fin 2 → Vec 2 → Vec 2) (T : Vec 2 → Mat 2)
    (hw : ∀ i k,MemLp (fun x => w i x k) 2 (normalizedCubeMeasure U))
    (hT : ∀ k l,MemLp (fun x => T x k l) 2 (normalizedCubeMeasure U)) (lam : ℝ) :
    HasSum (fun j : whiteBasisIndex => 2*lam*(∑ i : Fin 2,cubeAverage U (fun x =>
      vecDot ((cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))) • w i x)
        (matVecMul (T x) (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1))))
      (2*lam*(∑ i : Fin 2,cubeAverage U (fun x => vecDot (w i x)
        (matVecMul (T x) (matVecMul (oldHessianMeanCovariance Q U b L) (basisVec i)))))) := by
  let C := oldHessianMeanCovariance Q U b L
  let a := fun j => cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))
  let m := fun (j : whiteBasisIndex) (i : Fin 2) => (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1
  let A := fun (i l : Fin 2) => cubeAverage U (fun x => vecDot (w i x) (matVecMul (T x) (basisVec l)))
  have hs (i l : Fin 2) : HasSum (fun j => (a j*m j i l)*A i l) (C l i*A i l) :=
    (old_hessian_mean_covariance_entry Q fine b L U hU i l).1.hasSum.mul_right (A i l)
  have hh := (hasSum_sum (s := Finset.univ) (fun i _ =>
    hasSum_sum (s := Finset.univ) (fun l _ => hs i l))).mul_left (2*lam)
  have hmode (j : whiteBasisIndex) :
      (∑ i : Fin 2,cubeAverage U (fun x => vecDot (a j • w i x) (matVecMul (T x) (m j i))))=
        ∑ i : Fin 2,∑ l : Fin 2,(a j*m j i l)*A i l := by
    apply Finset.sum_congr rfl
    intro i _
    exact old_hessian_averaged_matrix_pairing U (w i) T (hw i) hT (a j) (m j i)
  have hlimit : (∑ i : Fin 2,cubeAverage U (fun x => vecDot (w i x)
      (matVecMul (T x) (matVecMul C (basisVec i)))))=
      ∑ i : Fin 2,∑ l : Fin 2,C l i*A i l := by
    apply Finset.sum_congr rfl
    intro i _
    have he := old_hessian_averaged_matrix_pairing U (w i) T (hw i) hT 1 (matVecMul C (basisVec i))
    simpa only [one_smul,one_mul,old_hessian_matrix_basis_column,A] using he
  rw [←hlimit] at hh
  exact hh.congr_fun (fun j => congrArg (fun x : ℝ => 2*lam*x) (hmode j))

end
end ASDExplicitGamma.Scalar
