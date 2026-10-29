module

public import ASDExplicitGamma.Scalar.OldHessianTrialTopReceiverField

/-! The actual local TOP reciprocal map is linear in its deterministic load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section

/-- Additivity of the genuine affine minimizer in its physical L2 class. -/
theorem old_hessian_canonical_add (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (P R : BlockVec 2) :
    oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (P+R)=
      oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P+
        oldSignedFrameCanonicalField Q nu sigma hnu hsigma k R := by
  apply Lp.ext
  filter_upwards with x
  simp only [oldSignedFrameCanonicalField,oldSignedCanonicalAffineField,map_add]

/-- Homogeneity of the same genuine affine minimizer. -/
theorem old_hessian_canonical_smul (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (c : ℝ) (P : BlockVec 2) :
    oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (c • P)=
      c • oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P := by
  simp only [oldSignedFrameCanonicalField,oldSignedCanonicalAffineField,map_smul]

/-- Exact two-column reconstruction in the actual affine Hilbert class. -/
theorem old_hessian_top_canonical_two_basis (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (e,0)=
      e 0 • oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec 0,0)+
        e 1 • oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec 1,0) := by
  have he : e=e 0 • basisVec 0+e 1 • basisVec 1 := by
    funext i
    fin_cases i <;> simp [basisVec]
  have hload : ((e,0) : BlockVec 2)=e 0 • (basisVec 0,0)+e 1 • (basisVec 1,0) :=
    Prod.ext he (by simp)
  rw [hload,old_hessian_canonical_add,old_hessian_canonical_smul,old_hessian_canonical_smul]

/-- The physical TOP reciprocal matrix consists of the same two local
canonical reciprocal columns as in the frozen covariance contraction. -/
def oldHessianCellTopReciprocalMatrix (Q U : TriadicCube 2) (hU : openCubeSet U⊆openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (x : Vec 2) : Mat 2 :=
  fun i j => oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k (basisVec j) x i

/-- Acting by the actual reciprocal matrix is exactly the actual local
TOP response at that load, a.e. on the same physical cell. -/
theorem old_hessian_cell_top_reciprocal_matrix_action (Q U : TriadicCube 2)
    (hU : openCubeSet U⊆openCubeSet Q) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    (fun x => matVecMul (oldHessianCellTopReciprocalMatrix Q U hU nu sigma hnu hsigma k x) e)=ᵐ[
      volumeMeasureOn (openCubeSet U)] oldHessianCellTopReciprocal Q U hU nu sigma hnu hsigma k e := by
  let kU := oldSignedCellCoefficient Q U hU k
  let S := oldSignedFrameCanonicalField U nu sigma hnu hsigma kU
  have hS := old_hessian_top_canonical_two_basis U nu sigma hnu hsigma kU e
  have hAe := Lp.ext_iff.mp hS
  filter_upwards [hAe,Lp.coeFn_add (e 0 • S (basisVec 0,0)) (e 1 • S (basisVec 1,0)),
    Lp.coeFn_smul (e 0) (S (basisVec 0,0)),Lp.coeFn_smul (e 1) (S (basisVec 1,0))] with x hx hadd h0 h1
  have hsx : S (e,0) x=e 0 • S (basisVec 0,0) x+e 1 • S (basisVec 1,0) x := by
    rw [hx,hadd]
    dsimp only [Pi.add_apply]
    rw [h0,h1]
    rfl
  unfold oldHessianCellTopReciprocalMatrix oldHessianCellTopReciprocal
  change matVecMul (fun i j => (blockMatVecMul
      (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (S (basisVec j,0) x)).2 i) e=
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x) (S (e,0) x)).2
  rw [hsx,blockMatVecMul_add,blockMatVecMul_smul,blockMatVecMul_smul]
  funext i
  dsimp only [matVecMul]
  rw [Fin.sum_univ_two]
  change (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x)
      (S (basisVec 0,0) x)).2 i*e 0+
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x)
      (S (basisVec 1,0) x)).2 i*e 1=
    e 0*(blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x)
      (S (basisVec 0,0) x)).2 i+
    e 1*(blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x)
      (S (basisVec 1,0) x)).2 i
  ring

end
end ASDExplicitGamma.Scalar
