module

public import ASDExplicitGamma.Scalar.CellResponseTest
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import Homogenization.CoarseGraining.OriginCubeSymmetry
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Geometry.TriadicCubeTranslation
public import Homogenization.Probability.Source.Coarse

/-! Covariance of the actual recovered cell response under a centered planar
quarter-turn.  The spatial and vector actions are assembled from the source
signed-permutation symmetries (one sign flip and one coordinate swap). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization Response Variational MeasureTheory

/-- Rotate the load in both block components by the source signed permutation
whose product is the clockwise planar quarter-turn. -/
noncomputable def quarterTurnLoad (P : BlockVec 2) : BlockVec 2 :=
  blockVecConj (Matrix.swap ℝ 0 1) (blockVecConj (signFlipMatrix 0) P)

/-- Pull a block state back by the centered quarter-turn of a triadic square.
The translation is to the centered origin cube, where the source's exact
sign-flip and swap actions are available. -/
noncomputable def quarterTurnCellState (Q : TriadicCube 2) (X : BlockState 2) : BlockState 2 :=
  (((X.translate (-triadicCubeShift Q)).signFlip 0).swap 0 1).translate
    (triadicCubeShift Q)

/-- Pull a coefficient back by the same centered quarter-turn and conjugate
its matrix action. -/
noncomputable def quarterTurnCellCoeff (Q : TriadicCube 2) (a : CoeffField 2) : CoeffField 2 :=
  translateCoeffField (-(triadicCubeShift Q))
    (rotateCoeffField (Matrix.swap ℝ 0 1)
      (rotateCoeffField (signFlipMatrix 0) (translateCoeffField (triadicCubeShift Q) a)))

private theorem scalarCellResponseTest_admissible
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    IsBlockMuAdmissible (openCubeSet Q) P (scalarCellResponseTest Q a hEll P) := by
  have h := scalar_cell_response_test_variation Q a hEll P
  refine ⟨memVectorL2_fst_of_memBlockL2 h.1, ?_,
    memVectorL2_snd_of_memBlockL2 h.1, ?_⟩
  · simpa [BlockState.eval] using h.2.1
  · simpa [BlockState.eval] using h.2.2

private theorem scalarCellResponseTest_energy_eq_Mu
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    blockEnergyAverage (openCubeSet Q) a (scalarCellResponseTest Q a hEll P) =
      Mu (openCubeSet Q) P a := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let _ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hU.isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData hU).toMuCorrectionSpaceRecoveryData
  let M := scalarCellSystem Q a hEll
  have hmu : ∀ T : BlockVec 2,
      Mu (openCubeSet Q) T a = M.toMuHilbertRealization.muCandidate T := by
    intro T
    exact (lemmaV_canonical_muCandidate_eq_Mu hU hEll
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) T).symm
  have h := R.recoveredField_blockEnergyAverage_eq_mu M hmu P
  simpa [R, M, scalarCellSystem, scalarCellResponseTest] using h

private theorem translate_ellipticity_to_origin {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ} (z : Vec d)
    (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) :=
      hEll.1.comp hshift
    have hEq :
        (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
          (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      have hadd_sub : x + z - z = x := by
        ext k
        simp [sub_eq_add_neg, add_assoc]
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hadd_sub]
          exact hx
        simp [hx, hxt]
        rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem] at hmem
          rw [hadd_sub] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hadd_sub : x + z - z = x := by
      ext k
      simp [sub_eq_add_neg, add_assoc]
    have hxt : x + z ∈ translateSet z U := by
      rw [mem_translateSet_iff_sub_mem, hadd_sub]
      exact hx
    exact hEll.2 (x + z) hxt

private theorem translate_ellipticity_from_origin {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ} (z : Vec d)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam (translateSet z U) (translateCoeffField (-z) a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x - z) :=
      (continuous_id.sub continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x - z ∈ U then a (x - z) i j else 0) :=
      hEll.1.comp hshift
    have hEq :
        (fun x i j => if x - z ∈ U then a (x - z) i j else 0) =
          (fun x i j => if x ∈ translateSet z U then
            translateCoeffField (-z) a x i j else 0) := by
      funext x i j
      have harg : x - z = (fun k => x k + -z k) := by
        ext k
        simp only [Pi.sub_apply]
        ring
      simp [harg, translateCoeffField, mem_translateSet_iff_sub_mem]
    simpa [hEq] using hcomp
  · intro x hx
    have hx' : x - z ∈ U := (mem_translateSet_iff_sub_mem).mp hx
    exact hEll.2 (x - z) hx'

private theorem rotate_ellipticity {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ} {R : Mat d}
    (hR : IsSignedPermutationMatrix R)
    (hU : ∀ x, x ∈ U ↔ matVecMul R x ∈ U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam U (rotateCoeffField R a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hRmeas : Measurable (fun x : Vec d => matVecMul R x) :=
      (continuous_matVecMul R).measurable
    have hmasked := hEll.1.comp hRmeas
    have hmaskedEntry (k l : Fin d) :
        Measurable (fun x : Vec d =>
          if matVecMul R x ∈ U then a (matVecMul R x) k l else 0) := by
      exact (measurable_pi_iff.mp ((measurable_pi_iff.mp hmasked) k)) l
    have hEntry (i j : Fin d) :
        Measurable (fun x : Vec d =>
          if x ∈ U then rotateCoeffField R a x i j else 0) := by
      let f (k l : Fin d) (x : Vec d) : ℝ :=
        (matTranspose R) i k *
          (if matVecMul R x ∈ U then a (matVecMul R x) k l else 0) * R l j
      have hf (k l : Fin d) : Measurable (f k l) := by
        dsimp [f]
        fun_prop
      have hsum : Measurable (fun x : Vec d => ∑ k, ∑ l, f k l x) := by
        apply Finset.measurable_sum
        intro k _
        apply Finset.measurable_sum
        intro l _
        exact hf k l
      have heq :
          (fun x : Vec d => if x ∈ U then rotateCoeffField R a x i j else 0) =
            (fun x => ∑ k, ∑ l, f k l x) := by
        funext x
        by_cases hx : x ∈ U
        · have hRx : matVecMul R x ∈ U := (hU x).mp hx
          simp [f, rotateCoeffField, Matrix.mul_apply, Finset.sum_mul,
            hx, hRx, mul_assoc]
          rw [Finset.sum_comm]
        · have hRx : matVecMul R x ∉ U := fun h => hx ((hU x).mpr h)
          simp [f, hx, hRx]
      simpa [heq] using hsum
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hEntry i j
  · intro x hx
    have hRx : matVecMul R x ∈ U := (hU x).mp hx
    simpa [rotateCoeffField] using
      Homogenization.Source.Coarse.isEllipticMatrix_rotate hR
        (hEll.2 (matVecMul R x) hRx)

theorem quarterTurnCellCoeff_isElliptic
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    IsEllipticFieldOn lam Lam (openCubeSet Q) (quarterTurnCellCoeff Q a) := by
  let z := triadicCubeShift Q
  let U := openCubeSet (originCube 2 Q.scale)
  let a0 := translateCoeffField z a
  let a1 := rotateCoeffField (signFlipMatrix 0) a0
  let a2 := rotateCoeffField (Matrix.swap ℝ 0 1) a1
  have hUQ : openCubeSet Q = translateSet z U := by
    simpa [z, U] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn lam Lam U a0 :=
    translate_ellipticity_to_origin z (by simpa [hUQ] using hEll)
  have hUflip : ∀ x, x ∈ U ↔ matVecMul (signFlipMatrix 0) x ∈ U := by
    intro x
    exact (mem_openCubeSet_originCube_signFlipMatrix_iff
      (m := Q.scale) (i := 0) (x := x)).symm
  have hEll1 : IsEllipticFieldOn lam Lam U a1 :=
    rotate_ellipticity (isSignedPermutationMatrix_signFlipMatrix 0) hUflip hEll0
  have hUswap : ∀ x, x ∈ U ↔ matVecMul (Matrix.swap ℝ 0 1) x ∈ U := by
    intro x
    exact (mem_openCubeSet_originCube_swap_iff
      (m := Q.scale) (i := 0) (j := 1) (x := x)).symm
  have hEll2 : IsEllipticFieldOn lam Lam U a2 :=
    rotate_ellipticity (isSignedPermutationMatrix_swap 0 1) hUswap hEll1
  rw [hUQ]
  simpa [quarterTurnCellCoeff, a2, a1, a0, z] using
    (translate_ellipticity_from_origin z hEll2)

/-- The source recovered affine cell minimizer is covariant under the centered
quarter-turn, for the coefficient pulled back and conjugated by that same
turn.  Ellipticity of the transformed coefficient is transported from the
original source witness through the exact translations and signed
permutations. -/
theorem scalar_cell_response_test_centered_quarterTurn_ae
    (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : BlockVec 2) :
    (scalarCellResponseTest Q (quarterTurnCellCoeff Q a)
      (quarterTurnCellCoeff_isElliptic Q a hEll)
      (quarterTurnLoad P)).eval =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (quarterTurnCellState Q (scalarCellResponseTest Q a hEll P)).eval := by
  let z := triadicCubeShift Q
  let U := openCubeSet (originCube 2 Q.scale)
  let X := scalarCellResponseTest Q a hEll P
  let Y := quarterTurnCellState Q X
  let a0 := translateCoeffField z a
  let a1 := rotateCoeffField (signFlipMatrix 0) a0
  let a2 := rotateCoeffField (Matrix.swap ℝ 0 1) a1
  let P2 := quarterTurnLoad P
  let X0 := X.translate (-z)
  let Y0 := (X0.signFlip 0).swap 0 1
  have hUQ : openCubeSet Q = translateSet z U := by
    simpa [z, U] using openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let hEllRot := quarterTurnCellCoeff_isElliptic Q a hEll
  have hArot : translateCoeffField z (quarterTurnCellCoeff Q a) = a2 := by
    ext x i j
    simp [quarterTurnCellCoeff, a2, a1, a0, z, translateCoeffField,
      add_assoc]
  have hYrot : Y.translate (-z) = Y0 := by
    apply BlockState.ext <;> funext x <;>
      simp [Y, Y0, X0, quarterTurnCellState, z, BlockState.translate]
  have hXadm : IsBlockMuAdmissible (openCubeSet Q) P X :=
    scalarCellResponseTest_admissible Q a hEll P
  have hX0 : IsBlockMuAdmissible U P X0 := by
    have h := isBlockMuAdmissible_translateSet (U := openCubeSet Q) hXadm (-z)
    simpa [X0, hUQ, U, z, translateSet_translateSet, BlockState.translate] using h
  have hX1 : IsBlockMuAdmissible U (blockVecConj (signFlipMatrix 0) P)
      (X0.signFlip 0) :=
    isBlockMuAdmissible_signFlip_openCubeSet_originCube hX0 0
  have hX2 : IsBlockMuAdmissible U P2 Y0 := by
    simpa [P2, Y0, quarterTurnLoad] using
      isBlockMuAdmissible_swap_openCubeSet_originCube hX1 0 1
  have hYL : Y = Y0.translate z := by
    apply BlockState.ext <;> funext x <;>
      simp [Y, Y0, X0, quarterTurnCellState, z, BlockState.translate]
  have hYadm : IsBlockMuAdmissible (openCubeSet Q) P2 Y := by
    have h := isBlockMuAdmissible_translateSet (U := U) hX2 z
    rw [hUQ, hYL]
    exact h
  have hEnergy0 : blockEnergyAverage U a2 Y0 = blockEnergyAverage U a0 X0 := by
    calc
      blockEnergyAverage U a2 Y0 =
          blockEnergyAverage U a1 (X0.signFlip 0) := by
            exact volumeAverage_blockEnergyDensity_swap_openCubeSet_originCube
              Q.scale a1 (X0.signFlip 0) 0 1
      _ = blockEnergyAverage U a0 X0 := by
            exact volumeAverage_blockEnergyDensity_signFlip_openCubeSet_originCube
              Q.scale a0 X0 0
  have hEnergy : blockEnergyAverage (openCubeSet Q)
        (quarterTurnCellCoeff Q a) Y = blockEnergyAverage (openCubeSet Q) a X := by
    rw [hUQ]
    rw [hYL]
    change volumeAverage (translateSet z U)
        (blockEnergyDensity (quarterTurnCellCoeff Q a) (Y0.translate z)) =
      volumeAverage (translateSet z U) (blockEnergyDensity a X)
    rw [volumeAverage_blockEnergyDensity_translate_forward z U
      (quarterTurnCellCoeff Q a) Y0]
    rw [hArot]
    have hXL : X = X0.translate z := by
      apply BlockState.ext <;> funext x <;> simp [X0, BlockState.translate, sub_eq_add_neg]
    rw [hXL]
    rw [volumeAverage_blockEnergyDensity_translate_forward z U a (X0)]
    exact hEnergy0
  have hMu0 : Mu U P2 a2 = Mu U P a0 := by
    calc
      Mu U P2 a2 = Mu U (blockVecConj (signFlipMatrix 0) P) a1 := by
        simpa [U, P2, a2, a1, quarterTurnLoad] using
          (Mu_swap_openCubeSet_originCube (d := 2) Q.scale
            (blockVecConj (signFlipMatrix 0) P) a1 0 1)
      _ = Mu U P a0 := by
        simpa [U, a1] using Mu_signFlip_openCubeSet_originCube
          (d := 2) Q.scale P a0 0
  have hMu : Mu (openCubeSet Q) P2 (quarterTurnCellCoeff Q a) =
      Mu (openCubeSet Q) P a := by
    calc
      Mu (openCubeSet Q) P2 (quarterTurnCellCoeff Q a) =
          Mu (translateSet z U) P2 (quarterTurnCellCoeff Q a) := by rw [hUQ]
      _ = Mu U P2 (translateCoeffField z (quarterTurnCellCoeff Q a)) :=
        Mu_translateSet_eq_translateCoeffField z U P2 (quarterTurnCellCoeff Q a)
      _ = Mu U P2 a2 := by rw [hArot]
      _ = Mu U P a0 := hMu0
      _ = Mu (translateSet z U) P a :=
        (Mu_translateSet_eq_translateCoeffField z U P a).symm
      _ = Mu (openCubeSet Q) P a := by rw [hUQ]
  have hYenergy : blockEnergyAverage (openCubeSet Q)
      (quarterTurnCellCoeff Q a) Y =
        Mu (openCubeSet Q) P2 (quarterTurnCellCoeff Q a) := by
    calc
      blockEnergyAverage (openCubeSet Q) (quarterTurnCellCoeff Q a) Y =
          blockEnergyAverage (openCubeSet Q) a X := hEnergy
      _ = Mu (openCubeSet Q) P a := scalarCellResponseTest_energy_eq_Mu Q a hEll P
      _ = Mu (openCubeSet Q) P2 (quarterTurnCellCoeff Q a) := hMu.symm
  let hU' := isOpenBoundedConvexDomain_openCubeSet Q
  let _ : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    hU'.isFiniteMeasure_restrict_volume
  let R := (lemmaVRecoveryData hU').toMuCorrectionSpaceRecoveryData
  let M := scalarCellSystem Q (quarterTurnCellCoeff Q a) hEllRot
  have hmu' : Mu (openCubeSet Q) P2 (quarterTurnCellCoeff Q a) =
      M.toMuHilbertRealization.muCandidate P2 := by
    exact (lemmaV_canonical_muCandidate_eq_Mu hU' hEllRot
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) P2).symm
  have hminY : toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval =
      M.toMuHilbertRealization.minimizerMap P2 := by
    apply M.toMuHilbertRealization.eq_minimizerMap_of_quadraticEnergy_le_muCandidate
      P2 (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) ?_ ?_
    · exact hYadm.toCorrectionFieldData_mem_correctionSpace
    · change quadraticEnergy (energyBilinOfOperator M.toMuOperatorRealization.operator)
        (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) ≤
          M.toMuHilbertRealization.muCandidate P2
      rw [M.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
        (X := Y) hYadm.memBlockL2_eval]
      rw [hYenergy, hmu']
  have hminTest : toHilbertBlockL2OfBlockField
      (scalar_cell_response_test_memL2 Q (quarterTurnCellCoeff Q a) hEllRot P2) =
      M.toMuHilbertRealization.minimizerMap P2 := by
    exact R.recoveredField_minimizer_eq M P2
  have hhilbert : toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval =
      toHilbertBlockL2OfBlockField
        (scalar_cell_response_test_memL2 Q (quarterTurnCellCoeff Q a) hEllRot P2) :=
    hminY.trans hminTest.symm
  have hYae : hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => Y.eval x := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval,
      coeFn_hilbertBlockL2ToBlockL2
        (toHilbertBlockL2OfBlockField hYadm.memBlockL2_eval)] with x hx hy
    rw [hy, hx]
    simp [hilbertifyBlockField]
  have hTae := lemmaV_recovered_minimizer_ae hU' hEllRot
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) P2
  have hTestAe : hilbertBlockL2ToBlockL2
      (toHilbertBlockL2OfBlockField
        (scalar_cell_response_test_memL2 Q (quarterTurnCellCoeff Q a) hEllRot P2)) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      (fun x => (scalarCellResponseTest Q (quarterTurnCellCoeff Q a) hEllRot P2).eval x) := by
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField
        (scalar_cell_response_test_memL2 Q (quarterTurnCellCoeff Q a) hEllRot P2),
      coeFn_hilbertBlockL2ToBlockL2
        (toHilbertBlockL2OfBlockField
          (scalar_cell_response_test_memL2 Q (quarterTurnCellCoeff Q a) hEllRot P2))]
      with x hx hy
    rw [hy, hx]
    simp [hilbertifyBlockField]
  have hL2eq := congrArg hilbertBlockL2ToBlockL2 hhilbert
  filter_upwards [hYae, hTestAe] with x hy ht
  have hx := congrArg (fun F : BlockL2 (openCubeSet Q) => F x) hL2eq
  rw [hy, ht] at hx
  exact hx.symm

end ASDExplicitGamma.Scalar

end
