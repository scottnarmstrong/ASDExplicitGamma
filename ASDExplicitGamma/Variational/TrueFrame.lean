module

public import ASDExplicitGamma.Model.Translation
public import ASDExplicitGamma.Variational.TraceDefect
public import Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.PrincipalResponseSwitchPlateau

/-! # The annealed response in the true homogenized frame

All scales are integers and all translation vectors are real. The frame is
`sigmaBar M m`; the molecular parameter `M.nu` is never substituted for it.
-/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization Homogenization.Book
open Algsuperdiff.Section3 MeasureTheory
open scoped Matrix.Norms.Elementwise

/-- Each expected framed entry equals the corresponding entry of the framed
annealed matrix. This uses the entrywise definition of the annealed matrix. -/
theorem integral_frameMatrix_entry (M : ABKModel 2) (m : ℤ)
    (U : Set (Vec 2)) (sigma : ℝ) (alpha beta : BlockCoord 2) :
    (∫ a : RegCoeffField 2,
      blockMatEntry (frameMatrix sigma (coarseBlockMatrix U a.toFun)) alpha beta
      ∂(Cutoff.coefficientCutoffLaw M m)) =
      blockMatEntry (frameMatrix sigma
        (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) U)) alpha beta := by
  cases alpha <;> cases beta <;>
    dsimp only [frameMatrix, blockMatEntry, Ch04.annealedBlockMatrix] <;>
    simp only [Matrix.smul_apply, smul_eq_mul, integral_const_mul] <;> rfl

/-- All framed coarse entries are integrable on every cutoff cube. -/
theorem integrable_frameMatrix_entry (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (sigma : ℝ) (alpha beta : BlockCoord 2) :
    Integrable (fun a : RegCoeffField 2 =>
      blockMatEntry (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a.toFun)) alpha beta)
      (Cutoff.coefficientCutoffLaw M m) := by
  have hentry := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M m Q
  cases alpha with
  | inl i =>
      cases beta with
      | inl j => exact (hentry (Sum.inl i) (Sum.inl j)).const_mul sigma⁻¹
      | inr j => exact hentry (Sum.inl i) (Sum.inr j)
  | inr i =>
      cases beta with
      | inl j => exact hentry (Sum.inr i) (Sum.inl j)
      | inr j => exact (hentry (Sum.inr i) (Sum.inr j)).const_mul sigma

/-- The genuine matrix-valued expectation equals the framed annealed matrix;
entrywise integrability is established, not imposed as an extra premise. -/
theorem integral_frameMatrix (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (sigma : ℝ) :
    (∫ a : RegCoeffField 2,
      toFullBlockMat (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a.toFun))
      ∂(Cutoff.coefficientCutoffLaw M m)) =
      toFullBlockMat (frameMatrix sigma
        (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q))) := by
  have hInt : Integrable (fun a : RegCoeffField 2 =>
      toFullBlockMat (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a.toFun)))
      (Cutoff.coefficientCutoffLaw M m) :=
    Integrable.of_eval fun alpha => Integrable.of_eval fun beta =>
      integrable_frameMatrix_entry M m Q sigma alpha beta
  ext alpha beta
  calc
    _ = (∫ a : RegCoeffField 2, fun beta =>
        toFullBlockMat (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a.toFun)) alpha beta
        ∂(Cutoff.coefficientCutoffLaw M m)) beta :=
      congrArg (fun row : BlockCoord 2 → ℝ => row beta)
        (eval_integral (fun alpha => hInt.eval alpha) alpha)
    _ = ∫ a : RegCoeffField 2,
        toFullBlockMat (frameMatrix sigma (coarseBlockMatrix (cubeSet Q) a.toFun)) alpha beta
        ∂(Cutoff.coefficientCutoffLaw M m) :=
      eval_integral (fun beta => (hInt.eval alpha).eval beta) beta
    _ = _ := integral_frameMatrix_entry M m (cubeSet Q) sigma alpha beta

/-- The unnormalized annealed response on any translated origin cube dominates
the true homogenized block matrix, at every integer scale. -/
theorem annealedBlockMatrix_trueFrame_lower (M : ABKModel 2) (m n : ℤ) (z : Vec 2) :
    BlockMatLoewnerLE
      (Ch02.blockDiag ((Annealed.sigmaBar M m : ℝ) • (1 : Mat 2))
        ((Annealed.sigmaBar M m : ℝ)⁻¹ • (1 : Mat 2)))
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
        (translateSet z (cubeSet (originCube 2 n)))) := by
  rw [Model.annealedBlockMatrix_translate_originCube]
  exact Provider.Diffusivity.ApproximateRecurrence.blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit
    M m n

/-- VA-TRUE-FRAME-MEAN: the normalized mean consists of two scalar blocks,
both at least one, independent of the real translation of the cube. -/
theorem exists_trueFrame_mean_scalars (M : ABKModel 2) (m n : ℤ) :
    ∃ alpha beta : ℝ, 1 ≤ alpha ∧ 1 ≤ beta ∧
      ∀ z : Vec 2,
        frameMatrix (Annealed.sigmaBar M m : ℝ)
          (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
            (translateSet z (cubeSet (originCube 2 n)))) =
          Ch02.blockDiag (alpha • (1 : Mat 2)) (beta • (1 : Mat 2)) := by
  obtain ⟨s, t, hst⟩ :=
    Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one
      M m n
  have hlim :=
    Provider.Diffusivity.ApproximateRecurrence.blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit
      M m n
  rw [hst] at hlim
  have hs := hlim (Pi.single (0 : Fin 2) 1, 0)
  have ht := hlim (0, Pi.single (0 : Fin 2) 1)
  dsimp only [Ch02.blockDiag, blockMatVecMul, blockVecDot] at hs ht
  simp [vecDot, matVecMul, Pi.single_apply] at hs ht
  have hsigma := (Annealed.sigmaBar_characterization M m).1
  have hs' : (Annealed.sigmaBar M m : ℝ) ≤ s := hs
  have ht' : (Annealed.sigmaBar M m : ℝ)⁻¹ ≤ t := ht
  refine ⟨(Annealed.sigmaBar M m : ℝ)⁻¹ * s,
    (Annealed.sigmaBar M m : ℝ) * t, ?_, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hs' (inv_nonneg.mpr hsigma.le)
    simpa only [inv_mul_cancel₀ hsigma.ne'] using h
  · have h := mul_le_mul_of_nonneg_left ht' hsigma.le
    simpa only [mul_inv_cancel₀ hsigma.ne'] using h
  · intro z
    rw [Model.annealedBlockMatrix_translate_originCube, hst]
    apply blockMat_ext <;> ext i j <;>
      simp [frameMatrix, Ch02.blockDiag, Matrix.smul_apply, smul_eq_mul, mul_assoc]

/-- Scalar block lower bounds imply the doubled identity lower bound. -/
theorem identity_le_scalar_blockDiag {alpha beta : ℝ}
    (ha : 1 ≤ alpha) (hb : 1 ≤ beta) :
    BlockMatLoewnerLE (Ch02.blockIdentity 2)
      (Ch02.blockDiag (alpha • (1 : Mat 2)) (beta • (1 : Mat 2))) := by
  intro P
  have hid (x : Vec 2) : matVecMul (1 : Mat 2) x = x := by
    exact Matrix.one_mulVec x
  have hz (x : Vec 2) : matVecMul (0 : Mat 2) x = 0 := by
    ext i
    simp [matVecMul]
  simp only [Ch02.blockIdentity, Ch02.blockDiag, blockMatVecMul, blockVecDot,
    smul_matVecMul, hid, hz, add_zero, zero_add, vecDot_smul_right]
  have hp := mul_le_mul_of_nonneg_right ha (vecNormSq_nonneg P.1)
  have hq := mul_le_mul_of_nonneg_right hb (vecNormSq_nonneg P.2)
  dsimp [vecNormSq] at hp hq
  linarith only [hp, hq]

/-- The annealed response in its true frame dominates I₄, for every translate
and every integer cube scale. -/
theorem trueFrame_mean_lower (M : ABKModel 2) (m n : ℤ) (z : Vec 2) :
    BlockMatLoewnerLE (Ch02.blockIdentity 2)
      (frameMatrix (Annealed.sigmaBar M m : ℝ)
        (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
          (translateSet z (cubeSet (originCube 2 n))))) := by
  obtain ⟨alpha, beta, ha, hb, hmean⟩ := exists_trueFrame_mean_scalars M m n
  rw [hmean z]
  exact identity_le_scalar_blockDiag ha hb

/-- The frozen trace defect is integrable on every cutoff cube. -/
theorem integrable_traceDefect_cutoffLaw (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (sigma : ℝ) :
    Integrable (fun a : RegCoeffField 2 => traceDefect (cubeSet Q) a.toFun sigma)
      (Cutoff.coefficientCutoffLaw M m) := by
  have hentry := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M m Q
  have hUL : Integrable (fun a : RegCoeffField 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft)
      (Cutoff.coefficientCutoffLaw M m) := by
    unfold Matrix.trace
    exact integrable_finsetSum _ (fun i _ => hentry (Sum.inl i) (Sum.inl i))
  have hLR : Integrable (fun a : RegCoeffField 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight)
      (Cutoff.coefficientCutoffLaw M m) := by
    unfold Matrix.trace
    exact integrable_finsetSum _ (fun i _ => hentry (Sum.inr i) (Sum.inr i))
  exact ((hUL.const_mul sigma⁻¹).add (hLR.const_mul sigma)).sub (integrable_const 4)

/-- Expectation of the frozen defect is the framed annealed trace minus four. -/
theorem integral_traceDefect_eq_annealed_trace (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (sigma : ℝ) :
    (∫ a : RegCoeffField 2, traceDefect (cubeSet Q) a.toFun sigma
      ∂(Cutoff.coefficientCutoffLaw M m)) =
      sigma⁻¹ * Matrix.trace
          (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q)).upperLeft +
        sigma * Matrix.trace
          (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q)).lowerRight - 4 := by
  have hentry := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M m Q
  have hUL : Integrable (fun a : RegCoeffField 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft)
      (Cutoff.coefficientCutoffLaw M m) :=
    integrable_finsetSum _ (fun i _ => hentry (Sum.inl i) (Sum.inl i))
  have hLR : Integrable (fun a : RegCoeffField 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight)
      (Cutoff.coefficientCutoffLaw M m) :=
    integrable_finsetSum _ (fun i _ => hentry (Sum.inr i) (Sum.inr i))
  simp only [traceDefect]
  rw [integral_sub (f := fun a : RegCoeffField 2 =>
      sigma⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft +
      sigma * Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight)
      ((hUL.const_mul sigma⁻¹).add (hLR.const_mul sigma)) (integrable_const 4),
    integral_add (f := fun a : RegCoeffField 2 =>
      sigma⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft)
      (g := fun a : RegCoeffField 2 =>
      sigma * Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight)
      (hUL.const_mul sigma⁻¹) (hLR.const_mul sigma), integral_const_mul,
    integral_const_mul, integral_const, probReal_univ, one_smul]
  congr 2
  · congr 1
    exact integral_finsetSum Finset.univ (fun i _ => hentry (Sum.inl i) (Sum.inl i))
  · congr 1
    exact integral_finsetSum Finset.univ (fun i _ => hentry (Sum.inr i) (Sum.inr i))

/-- Mean trace defects are independent of every real translation. -/
theorem integral_traceDefect_translate_originCube (M : ABKModel 2) (m n : ℤ)
    (z : Vec 2) (sigma : ℝ) :
    (∫ a : RegCoeffField 2,
      traceDefect (translateSet z (cubeSet (originCube 2 n))) a.toFun sigma
      ∂(Cutoff.coefficientCutoffLaw M m)) =
    ∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 n)) a.toFun sigma
      ∂(Cutoff.coefficientCutoffLaw M m) :=
  Provider.Annealed.integral_comp_toFun_translation_transfer_real
    (X := fun U a => traceDefect U a sigma)
    (U := cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoffLaw_stationary_real M m)
    (Model.aemeasurable_traceDefect_cutoffLaw M m _ sigma).aestronglyMeasurable
    (fun U z a => Model.traceDefect_translate U z a sigma) z

/-- Scalar block upper bounds give the corresponding doubled matrix bound. -/
theorem scalar_blockDiag_le_scalar_identity {alpha beta c : ℝ}
    (ha : alpha ≤ c) (hb : beta ≤ c) :
    BlockMatLoewnerLE
      (Ch02.blockDiag (alpha • (1 : Mat 2)) (beta • (1 : Mat 2)))
      (Ch02.blockDiag (c • (1 : Mat 2)) (c • (1 : Mat 2))) := by
  intro P
  have hid (x : Vec 2) : matVecMul (1 : Mat 2) x = x := Matrix.one_mulVec x
  have hz (x : Vec 2) : matVecMul (0 : Mat 2) x = 0 := by
    ext i
    simp [matVecMul]
  simp only [Ch02.blockDiag, blockMatVecMul, blockVecDot,
    smul_matVecMul, hid, hz, add_zero, zero_add, vecDot_smul_right]
  have hp := mul_le_mul_of_nonneg_right ha (vecNormSq_nonneg P.1)
  have hq := mul_le_mul_of_nonneg_right hb (vecNormSq_nonneg P.2)
  dsimp [vecNormSq] at hp hq
  linarith only [hp, hq]

/-- VA-TRUE-FRAME-MEAN with its trace cap: a cap at any translated cell bounds
both scalar blocks, and hence the mean matrix, at every translate of that scale. -/
theorem exists_trueFrame_mean_bounds (M : ABKModel 2) (m n : ℤ) (z : Vec 2)
    {C : ℝ}
    (htrace : (∫ a : RegCoeffField 2,
      traceDefect (translateSet z (cubeSet (originCube 2 n))) a.toFun
        (Annealed.sigmaBar M m : ℝ) ∂(Cutoff.coefficientCutoffLaw M m)) ≤ C) :
    ∃ alpha beta : ℝ, 1 ≤ alpha ∧ 1 ≤ beta ∧
      alpha ≤ 1 + C / 2 ∧ beta ≤ 1 + C / 2 ∧
      ∀ w : Vec 2,
        frameMatrix (Annealed.sigmaBar M m : ℝ)
          (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
            (translateSet w (cubeSet (originCube 2 n)))) =
          Ch02.blockDiag (alpha • (1 : Mat 2)) (beta • (1 : Mat 2)) ∧
        BlockMatLoewnerLE
          (frameMatrix (Annealed.sigmaBar M m : ℝ)
            (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
              (translateSet w (cubeSet (originCube 2 n)))))
          (Ch02.blockDiag ((1 + C / 2) • (1 : Mat 2)) ((1 + C / 2) • (1 : Mat 2))) := by
  obtain ⟨alpha, beta, ha, hb, hmean⟩ := exists_trueFrame_mean_scalars M m n
  have hzero := hmean 0
  rw [translateSet_zero] at hzero
  have hUL := congrArg (fun A : BlockMat 2 => Matrix.trace A.upperLeft) hzero
  have hLR := congrArg (fun A : BlockMat 2 => Matrix.trace A.lowerRight) hzero
  simp only [frameMatrix, Ch02.blockDiag, Matrix.trace_smul, smul_eq_mul,
    Matrix.trace_one, Fintype.card_fin] at hUL hLR
  rw [integral_traceDefect_translate_originCube,
    integral_traceDefect_eq_annealed_trace] at htrace
  rw [hUL, hLR] at htrace
  norm_num only [Nat.cast_ofNat] at htrace
  have hsum : 2 * alpha + 2 * beta - 4 ≤ C := by
    linarith only [htrace]
  have haC : alpha ≤ 1 + C / 2 := by linarith only [hsum, hb]
  have hbC : beta ≤ 1 + C / 2 := by linarith only [hsum, ha]
  refine ⟨alpha, beta, ha, hb, haC, hbC, ?_⟩
  intro w
  refine ⟨hmean w, ?_⟩
  rw [hmean w]
  exact scalar_blockDiag_le_scalar_identity haC hbC

/-- The source conclusion directly as a matrix-valued expectation on an
arbitrary triadic cell, with the source trace-cap premise and no extra data. -/
theorem exists_trueFrame_cube_mean_bounds (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) {C : ℝ}
    (htrace : (∫ a : RegCoeffField 2, traceDefect (cubeSet Q) a.toFun
      (Annealed.sigmaBar M m : ℝ) ∂(Cutoff.coefficientCutoffLaw M m)) ≤ C) :
    ∃ alpha beta : ℝ, 1 ≤ alpha ∧ 1 ≤ beta ∧
      alpha ≤ 1 + C / 2 ∧ beta ≤ 1 + C / 2 ∧
      (∫ a : RegCoeffField 2,
        toFullBlockMat (frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet Q) a.toFun))
        ∂(Cutoff.coefficientCutoffLaw M m)) =
        toFullBlockMat (Ch02.blockDiag (alpha • (1 : Mat 2)) (beta • (1 : Mat 2))) := by
  have hcap : (∫ a : RegCoeffField 2,
      traceDefect (translateSet (triadicCubeShift Q)
        (cubeSet (originCube 2 Q.scale))) a.toFun (Annealed.sigmaBar M m : ℝ)
      ∂(Cutoff.coefficientCutoffLaw M m)) ≤ C := by
    rwa [← cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  obtain ⟨alpha, beta, ha, hb, haC, hbC, hmean⟩ :=
    exists_trueFrame_mean_bounds M m Q.scale (triadicCubeShift Q) hcap
  refine ⟨alpha, beta, ha, hb, haC, hbC, ?_⟩
  rw [integral_frameMatrix]
  have heq := (hmean (triadicCubeShift Q)).1
  rw [← cubeSet_eq_translateSet_originCube_of_triadicCube Q] at heq
  exact congrArg toFullBlockMat heq

end ASDExplicitGamma.Variational
