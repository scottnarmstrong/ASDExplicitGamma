module

public import ASDExplicitGamma.Triadic.SensitivityPathCoefficient
public import ASDExplicitGamma.Variational.AdapterConstantSkew
public import ASDExplicitGamma.Variational.EnergyMap
public import Homogenization.Book.Ch02.Theorems.DoubledMu

/-! Constant-skew gauge invariance for the finite inverse-lambda history. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational

noncomputable section

private theorem sensitivity_constantSkewCongruence_quadratic (g : ℝ)
    (A : BlockMat 2) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (constantSkewCongruence g A) P) =
      blockVecDot (constantSkewLoad g P) (blockMatVecMul A (constantSkewLoad g P)) := by
  have hmul (g : ℝ) (P : BlockVec 2) :
      Matrix.mulVec (constantSkewMatrix g) (toFullBlockVec P) =
        toFullBlockVec (constantSkewLoad g P) := by
    unfold constantSkewMatrix
    rw [← toFullBlockVec_blockMatVecMul]
    congr 1
    ext i <;> fin_cases i <;> simp [blockMatVecMul, constantSkewLoad,
      matVecMul, Fin.sum_univ_two, responsePlanarJ] <;> ring
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  simp only [constantSkewCongruence, toFullBlockMat_ofFullBlockMat,
    ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hmul]
  rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]

private theorem sensitivity_constantSkewCongruence_symmetric (g : ℝ)
    (A : BlockMat 2) (hA : IsSymmetricBlockMat A) :
    IsSymmetricBlockMat (constantSkewCongruence g A) := by
  apply isSymmetricBlockMat_of_isSymm
  have hfull : (toFullBlockMat A).IsSymm := by
    ext α β
    exact hA β α
  change ((constantSkewMatrix g).transpose * toFullBlockMat A *
    constantSkewMatrix g).transpose = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hfull]
  exact (Matrix.mul_assoc (constantSkewMatrix g).transpose (toFullBlockMat A)
    (constantSkewMatrix g)).symm

/-- Restriction commutes with adding a constant skew amplitude. -/
theorem sensitivityResponseCoefficientRestrict_add_const
    {Q R : TriadicCube 2} {j : ℕ}
    (k : ResponseCoefficient (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) (g : ℝ) :
    sensitivityResponseCoefficientRestrict
        (k + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) hR =
      sensitivityResponseCoefficientRestrict k hR +
        BoundedContinuousFunction.const (closure (openCubeSet R)) g := by
  ext x
  simp [sensitivityResponseCoefficientRestrict,
    BoundedContinuousFunction.compContinuous_apply]

/-- An affine coefficient path transports a constant shift by the path time. -/
theorem sensitivityResponseCoefficientPath_add_const
    {Q : TriadicCube 2} (k kH : ResponseCoefficient (openCubeSet Q))
    (g t : ℝ) :
    sensitivityResponseCoefficientPath k
        (kH + BoundedContinuousFunction.const (closure (openCubeSet Q)) g) t =
      sensitivityResponseCoefficientPath k kH t +
        BoundedContinuousFunction.const (closure (openCubeSet Q)) (t * g) := by
  ext x
  simp [sensitivityResponseCoefficientPath]
  ring

theorem sensitivityBookCoeffOn_constantShift_sigmaStarInv
    (Q : TriadicCube 2) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient (openCubeSet Q)) (g : ℝ) :
    Homogenization.Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν
          (k + BoundedContinuousFunction.const (closure (openCubeSet Q)) g)) =
      Homogenization.Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν k) := by
  let U := openCubeSet Q
  let c : ResponseCoefficient U := BoundedContinuousFunction.const (closure U) g
  let a := sensitivityBookCoeffOn Q ν hν k
  let b := sensitivityBookCoeffOn Q ν hν (k + c)
  let F : CoeffField 2 := responsePlanarCoefficientField ν k
  let G : CoeffField 2 := fun x =>
    responsePlanarCoefficient ν (responseCoefficientExtension k x + g)
  have hrestrictA : restrictCoeffField U a.toCoeffField = restrictCoeffField U F := by
    funext x
    by_cases hx : x ∈ U
    · simp [restrictCoeffField, hx, a, F, sensitivityBookCoeffOn,
        responseFramePlanarCoefficientField, responsePlanarCoefficientField, div_one]
    · simp [restrictCoeffField, hx]
  have hrestrictB : restrictCoeffField U b.toCoeffField = restrictCoeffField U G := by
    funext x
    by_cases hx : x ∈ U
    · simp only [restrictCoeffField, hx]
      simp only [b, sensitivityBookCoeffOn, responseFramePlanarCoefficientField, div_one]
      rw [responseCoefficientExtension_add_on k c hx,
        responseCoefficientExtension_eq c hx]
      simp [c]
      ext i j
      fin_cases i <;> fin_cases j
      all_goals simp [G, responsePlanarCoefficient, responsePlanarJ,
        Matrix.smul_apply, smul_eq_mul]
    · simp [restrictCoeffField, hx]
  have hEllA : IsEllipticFieldOn a.lam a.Lam U a.toCoeffField := by
    simpa [a, sensitivityBookCoeffOn, responseFramePlanarCoefficientField,
      div_one] using
        responseFramePlanarCoefficientField_isElliptic
          (measurableSet_openCubeSet Q) ν 1 hν one_pos k
  have hEllB : IsEllipticFieldOn b.lam b.Lam U b.toCoeffField := by
    simpa [b, sensitivityBookCoeffOn, responseFramePlanarCoefficientField,
      div_one, c] using
        responseFramePlanarCoefficientField_isElliptic
          (measurableSet_openCubeSet Q) ν 1 hν one_pos (k + c)
  have hBookA := Variational.energyMap_coarseBlockMatrix_eq (Book.Ch02.cubeDomain Q) a hEllA
  have hBookB := Variational.energyMap_coarseBlockMatrix_eq (Book.Ch02.cubeDomain Q) b hEllB
  have hMuA (P : BlockVec 2) : Mu U P a.toCoeffField =
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (Homogenization.coarseBlockMatrix U a.toCoeffField) P) := by
    calc
      Mu U P a.toCoeffField = Book.Ch02.doubledMu (Book.Ch02.cubeDomain Q) a P :=
        (Homogenization.Internal.Ch02.BookCh02.book_doubledMu_eq_Mu
          (Book.Ch02.cubeDomain Q) a P).symm
    _ = (1 / 2 : ℝ) * blockVecDot P
          (blockMatVecMul
            (Homogenization.coarseBlockMatrix U a.toCoeffField) P) := by
        rw [(Book.Ch02.doubledMuTheory (Book.Ch02.cubeDomain Q) a).doubledMu_eq_coarseBlockMatrix P,
          hBookA]
        simp only [Book.Ch02.cubeDomain_coe]
        rfl
  have hCoarseA : Homogenization.coarseBlockMatrix U a.toCoeffField =
      Homogenization.coarseBlockMatrix U F := by
    apply Homogenization.coarseBlockMatrix_eq_of_mu_eq
    intro P
    calc
      Mu U P a.toCoeffField = Mu U P (restrictCoeffField U a.toCoeffField) :=
        (Mu_restrictCoeffField_eq (measurableSet_openCubeSet Q) P a.toCoeffField).symm
      _ = Mu U P (restrictCoeffField U F) := by rw [hrestrictA]
      _ = Mu U P F := Mu_restrictCoeffField_eq (measurableSet_openCubeSet Q) P F
  have hMuBase (P : BlockVec 2) : Mu U P F =
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (Homogenization.coarseBlockMatrix U F) P) := by
    calc
      Mu U P F = Mu U P (restrictCoeffField U F) :=
        (Mu_restrictCoeffField_eq (measurableSet_openCubeSet Q) P F).symm
      _ = Mu U P (restrictCoeffField U a.toCoeffField) := by rw [hrestrictA]
      _ = Mu U P a.toCoeffField :=
        Mu_restrictCoeffField_eq (measurableSet_openCubeSet Q) P a.toCoeffField
      _ = _ := hMuA P
      _ = _ := by rw [hCoarseA]
  have hMuGauge (P : BlockVec 2) : Mu U P b.toCoeffField =
      Mu U (constantSkewLoad g P) F := by
    calc
      Mu U P b.toCoeffField = Mu U P (restrictCoeffField U b.toCoeffField) :=
        (Mu_restrictCoeffField_eq (measurableSet_openCubeSet Q) P b.toCoeffField).symm
      _ = Mu U P (restrictCoeffField U G) := by rw [hrestrictB]
      _ = Mu U P G := Mu_restrictCoeffField_eq (measurableSet_openCubeSet Q) P G
      _ = Mu U (constantSkewLoad g P) F := by
        exact Variational.Mu_constantSkew ν hν
          (responseCoefficientExtension k) g P
  have hAcoarse : IsSymmetricBlockMat (Homogenization.coarseBlockMatrix U F) :=
    Variational.coarseBlockMatrix_symmetric U F
  have hB : Homogenization.IsCoarseBlockMatrix U b.toCoeffField
      (constantSkewCongruence g (Homogenization.coarseBlockMatrix U F)) := by
    constructor
    · exact sensitivity_constantSkewCongruence_symmetric g _ hAcoarse
    · intro P
      calc
        Mu U P b.toCoeffField = Mu U (constantSkewLoad g P) F := hMuGauge P
        _ = (1 / 2 : ℝ) * blockVecDot (constantSkewLoad g P)
            (blockMatVecMul (Homogenization.coarseBlockMatrix U F)
              (constantSkewLoad g P)) := hMuBase _
        _ = (1 / 2 : ℝ) * blockVecDot P
            (blockMatVecMul
              (constantSkewCongruence g (Homogenization.coarseBlockMatrix U F)) P) := by
          rw [sensitivity_constantSkewCongruence_quadratic]
  have hcov := Homogenization.eq_coarseBlockMatrix_of_isCoarseBlockMatrix hB
  calc
    Homogenization.Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) b =
        (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) b).lowerRight := by rfl
    _ = (Homogenization.coarseBlockMatrix U b.toCoeffField).lowerRight := by
      simpa [U, Book.Ch02.cubeDomain_coe] using
        (congrArg (fun A : BlockMat 2 => A.lowerRight) hBookB)
    _ = (constantSkewCongruence g (Homogenization.coarseBlockMatrix U F)).lowerRight :=
      congrArg (fun A : BlockMat 2 => A.lowerRight) hcov.symm
    _ = (Homogenization.coarseBlockMatrix U F).lowerRight :=
      Variational.constantSkewCongruence_lowerRight g _
    _ = (Homogenization.coarseBlockMatrix U a.toCoeffField).lowerRight := by
      rw [hCoarseA]
    _ = (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) a).lowerRight := by
      simpa [U, Book.Ch02.cubeDomain_coe] using
        (congrArg (fun A : BlockMat 2 => A.lowerRight) hBookA).symm
    _ = Homogenization.Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) a := by rfl

end

end ASDExplicitGamma.Triadic
