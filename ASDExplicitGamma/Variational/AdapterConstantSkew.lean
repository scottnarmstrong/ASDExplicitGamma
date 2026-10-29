module

public import ASDExplicitGamma.Variational.AdapterMu
public import Algsuperdiff.Section3.Provider.Affine.H10SkewDivergence
public import Algsuperdiff.Section4.Provider.ExcessDecay.AntisymmetricShift

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

/-- A constant skew matrix has zero distributional divergence on gradients. -/
theorem constant_skew_gradient_isSolenoidal {d : ℕ} {U : Set (Vec d)}
    {C : Mat d} (hC : matTranspose C = -C) (u : H1Function U) :
    IsSolenoidalOn U (fun x => matVecMul C (u.grad x)) :=
  Algsuperdiff.Section4.Provider.ExcessDecay.integral_vecDot_matVecMul_skew_h10 hC u

/-- A quarter-turned zero-trace gradient has zero normal trace. -/
theorem planarJ_gradient_isSolenoidalZeroNormalTrace {U : Set (Vec 2)}
    (u : H10Function U) :
    IsSolenoidalZeroNormalTraceOn U (fun x => matVecMul responsePlanarJ (u.toH1Function.grad x)) := by
  intro φ
  have h := Algsuperdiff.Section3.Provider.Affine.integral_grad_swap u φ 0 1
  have h0 : Integrable (fun x => u.toH1Function.grad x 0 * φ.grad x 1) (volume.restrict U) :=
    (u.toH1Function.gradMemL2 0).integrable_mul (φ.gradMemL2 1)
  have h1 : Integrable (fun x => u.toH1Function.grad x 1 * φ.grad x 0) (volume.restrict U) :=
    (u.toH1Function.gradMemL2 1).integrable_mul (φ.gradMemL2 0)
  have hp : (fun x => vecDot (matVecMul responsePlanarJ (u.toH1Function.grad x))
      (φ.grad x)) = fun x => -(u.toH1Function.grad x 1 * φ.grad x 0) +
        u.toH1Function.grad x 0 * φ.grad x 1 := by
    funext x
    simp [vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two]
  rw [hp]
  have hi : (∫ x in U, -(u.toH1Function.grad x 1 * φ.grad x 0) +
      u.toH1Function.grad x 0 * φ.grad x 1) =
      -(∫ x in U, u.toH1Function.grad x 1 * φ.grad x 0) +
      ∫ x in U, u.toH1Function.grad x 0 * φ.grad x 1 := by
    calc
      _ = (∫ x in U, -(u.toH1Function.grad x 1 * φ.grad x 0)) +
          ∫ x in U, u.toH1Function.grad x 0 * φ.grad x 1 := integral_add h1.neg h0
      _ = _ := by rw [integral_neg]
  rw [hi]
  have hc : (∫ x in U, u.toH1Function.grad x 1 * φ.grad x 0) =
      ∫ x in U, u.toH1Function.grad x 0 * φ.grad x 1 := by
    simpa only [mul_comm] using h
  rw [hc]
  ring

private theorem memVectorL2_planarJ {U : Set (Vec 2)} {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) : MemVectorL2 U (fun x => matVecMul responsePlanarJ (f x)) := by
  apply MemLp.of_eval
  intro i
  fin_cases i
  · have he : (fun x => matVecMul responsePlanarJ (f x) 0) = -(fun x => f x 1) := by
      funext x
      simp [matVecMul, responsePlanarJ, Fin.sum_univ_two]
    change MemLp (fun x => matVecMul responsePlanarJ (f x) 0) 2 (volumeMeasureOn U)
    rw [he]
    exact (hf.eval 1).neg
  · simpa [matVecMul, responsePlanarJ, Fin.sum_univ_two] using hf.eval 0

/-- The physical constant-skew load shear. -/
def constantSkewLoad (g : ℝ) (P : BlockVec 2) : BlockVec 2 :=
  (P.1, P.2 - g • matVecMul responsePlanarJ P.1)

private def constantSkewState (g : ℝ) (X : BlockState 2) : BlockState 2 :=
  { potential := X.potential
    flux := fun x => X.flux x - g • matVecMul responsePlanarJ (X.potential x) }

private theorem admissible_constantSkewState {U : Set (Vec 2)}
    {P : BlockVec 2} {X : BlockState 2} (hX : IsBlockMuAdmissible U P X) (g : ℝ) :
    IsBlockMuAdmissible U (constantSkewLoad g P) (constantSkewState g X) := by
  let f := fun x => X.flux x - P.2
  let h := fun x => matVecMul responsePlanarJ (X.potential x - P.1)
  have hh : MemVectorL2 U h := memVectorL2_planarJ hX.1
  have hs : IsSolenoidalZeroNormalTraceOn U h := by
    obtain ⟨u, hu⟩ := hX.2.1
    change u.toH1Function.grad = (fun x => X.potential x - P.1) at hu
    have he : h = (fun x => matVecMul responsePlanarJ (u.toH1Function.grad x)) :=
      congrArg (fun f : Vec 2 → Vec 2 => fun x => matVecMul responsePlanarJ (f x)) hu.symm
    rw [he]
    exact planarJ_gradient_isSolenoidalZeroNormalTrace u
  have he : (fun x => (constantSkewState g X).flux x - (constantSkewLoad g P).2) =
      f + (-g) • h := by
    funext x i
    simp [f, h, constantSkewState, constantSkewLoad, matVecMul, Finset.sum_sub_distrib, mul_sub]
    ring
  refine ⟨hX.1, hX.2.1, ?_, ?_⟩
  · rw [he]
    exact hX.2.2.1.add (hh.const_smul (-g))
  · rw [he]
    apply isSolenoidalZeroNormalTraceOn_add hX.2.2.2
      (isSolenoidalZeroNormalTraceOn_smul hs (-g))
    · intro φ
      exact integrableOn_vecDot_of_memVectorL2 hX.2.2.1 φ.grad_memVectorL2
    · intro φ
      exact integrableOn_vecDot_of_memVectorL2 (hh.const_smul (-g)) φ.grad_memVectorL2

private theorem constantSkewState_neg (g : ℝ) (X : BlockState 2) :
    constantSkewState g (constantSkewState (-g) X) = X := by
  apply BlockState.ext
  · rfl
  · ext x i
    simp [constantSkewState]

private theorem constantSkewLoad_neg (g : ℝ) (P : BlockVec 2) :
    constantSkewLoad (-g) (constantSkewLoad g P) = P := by
  ext <;> simp [constantSkewLoad]

private theorem blockEnergyDensity_planar (ν κ : ℝ) (hν : ν ≠ 0)
    (X : BlockState 2) (x : Vec 2) :
    blockEnergyDensity (fun _ => responsePlanarCoefficient ν κ) X x =
      (1 / 2 : ℝ) * responseFrameEnergyDensity ν 1 κ (X.eval x) := by
  have h := responseFrameEnergyDensity_eq_blockMatrix ν 1 κ hν (by norm_num) (X.eval x)
  have hf (A : BlockMat 2) : frameMatrix 1 A = A := by
    cases A
    simp [frameMatrix]
  rw [hf] at h
  exact congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) h.symm

private theorem blockEnergyDensity_constantSkew (ν : ℝ) (κ : Vec 2 → ℝ)
    (hν : ν ≠ 0) (g : ℝ) (X : BlockState 2) (x : Vec 2) :
    blockEnergyDensity (fun y => responsePlanarCoefficient ν (κ y + g)) X x =
      blockEnergyDensity (fun y => responsePlanarCoefficient ν (κ y))
        (constantSkewState g X) x := by
  change blockEnergyDensity (fun _ => responsePlanarCoefficient ν (κ x + g)) X x =
    blockEnergyDensity (fun _ => responsePlanarCoefficient ν (κ x)) (constantSkewState g X) x
  rw [blockEnergyDensity_planar ν (κ x + g) hν,
    blockEnergyDensity_planar ν (κ x) hν, responseFrameEnergyDensity_shear]
  congr 2
  ext i <;> simp [responseShear, responseShearCorrection, constantSkewState, BlockState.eval,
    sub_eq_add_neg]

/-- The exact constant-skew gauge identity for the actual variational minimum.
It holds without an ellipticity premise on the measurable domain. -/
theorem Mu_constantSkew {U : Set (Vec 2)} (ν : ℝ) (hν : 0 < ν)
    (κ : Vec 2 → ℝ) (g : ℝ) (P : BlockVec 2) :
    Mu U P (fun x => responsePlanarCoefficient ν (κ x + g)) =
      Mu U (constantSkewLoad g P) (fun x => responsePlanarCoefficient ν (κ x)) := by
  unfold Mu
  congr 1
  ext t
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨constantSkewState g X, admissible_constantSkewState hX g, ?_⟩
    exact congrArg (volumeAverage U) (funext (blockEnergyDensity_constantSkew ν κ hν.ne' g X))
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨constantSkewState (-g) Y, ?_, ?_⟩
    · simpa only [constantSkewLoad_neg] using admissible_constantSkewState hY (-g)
    · have he := congrArg (volumeAverage U)
        (funext (blockEnergyDensity_constantSkew ν κ hν.ne' g (constantSkewState (-g) Y)))
      rw [constantSkewState_neg] at he
      exact he.symm

/-- The full matrix of the physical load shear. -/
def constantSkewMatrix (g : ℝ) : FullBlockMat 2 :=
  toFullBlockMat
    { upperLeft := 1
      upperRight := 0
      lowerLeft := -g • responsePlanarJ
      lowerRight := 1 }

private theorem constantSkewMatrix_mulVec (g : ℝ) (P : BlockVec 2) :
    Matrix.mulVec (constantSkewMatrix g) (toFullBlockVec P) =
      toFullBlockVec (constantSkewLoad g P) := by
  unfold constantSkewMatrix
  rw [← toFullBlockVec_blockMatVecMul]
  congr 1
  ext i <;> fin_cases i <;> simp [blockMatVecMul, constantSkewLoad,
    matVecMul, Fin.sum_univ_two, responsePlanarJ] <;> ring

/-- Congruence by the physical constant-skew load shear. -/
def constantSkewCongruence (g : ℝ) (A : BlockMat 2) : BlockMat 2 :=
  ofFullBlockMat ((constantSkewMatrix g).transpose * toFullBlockMat A * constantSkewMatrix g)

private theorem constantSkewCongruence_quadratic (g : ℝ) (A : BlockMat 2)
    (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (constantSkewCongruence g A) P) =
      blockVecDot (constantSkewLoad g P) (blockMatVecMul A (constantSkewLoad g P)) := by
  rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul]
  simp only [constantSkewCongruence, toFullBlockMat_ofFullBlockMat,
    ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, constantSkewMatrix_mulVec]
  rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]

private theorem constantSkewCongruence_symmetric (g : ℝ) (A : BlockMat 2)
    (hA : IsSymmetricBlockMat A) : IsSymmetricBlockMat (constantSkewCongruence g A) := by
  apply isSymmetricBlockMat_of_isSymm
  have ha : (toFullBlockMat A).IsSymm := by
    ext α β
    exact (hA β α)
  change ((constantSkewMatrix g).transpose * toFullBlockMat A * constantSkewMatrix g).transpose = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ha]
  exact (Matrix.mul_assoc (constantSkewMatrix g).transpose (toFullBlockMat A) (constantSkewMatrix g)).symm

/-- The actual coarse matrix transforms by constant-skew congruence. -/
theorem coarseBlockMatrix_constantSkew {Q : TriadicCube 2}
    (ν : ℝ) (hν : 0 < ν) (κ : Vec 2 → ℝ) {Λ : ℝ}
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (κ x))) (g : ℝ) :
    coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x + g)) =
      constantSkewCongruence g
        (coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x))) := by
  apply Eq.symm
  apply eq_coarseBlockMatrix_of_isCoarseBlockMatrix
  refine ⟨constantSkewCongruence_symmetric _ _ (coarseBlockMatrix_symmetric _ _), ?_⟩
  intro P
  rw [Mu_constantSkew ν hν, mu_eq_half_coarseBlockMatrix_elliptic_triCube hν hEll,
    constantSkewCongruence_quadratic]

/-- Source specialization: bounded continuous skew amplitudes require no
additional ellipticity hypothesis. -/
theorem response_coarseBlockMatrix_constantSkew (Q : TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (cubeSet Q)) (g : ℝ) :
    coarseBlockMatrix (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + g)) =
      constantSkewCongruence g (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField ν k)) :=
  coarseBlockMatrix_constantSkew ν hν (responseCoefficientExtension k)
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k) g

/-- The reciprocal block is exactly invariant under a constant skew shift. -/
theorem constantSkewCongruence_lowerRight (g : ℝ) (A : BlockMat 2) :
    (constantSkewCongruence g A).lowerRight = A.lowerRight := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [constantSkewCongruence, constantSkewMatrix, ofFullBlockMat, toFullBlockMat,
      Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      responsePlanarJ]

end

end ASDExplicitGamma.Variational
