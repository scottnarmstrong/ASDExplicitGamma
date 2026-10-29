module

public import ASDExplicitGamma.Gaussian.FixedNuBounds
public import Homogenization.CoarseGraining.CoarseBounds.Sandwich
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

/-! Elliptic normalization and positivity of the fixed-frame inverse block.
The normalization and translation proofs reuse the arguments of the private
helpers in Variational.TraceDefect, now exposed in a focused reusable module. -/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational

theorem fixedNu_matrix_normalize {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix 1 (Lam / lam) (lam⁻¹ • A) := by
  rcases hA with ⟨hlam, hle, hlower, hinv⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix ⟨hlam, hle, hlower, hinv⟩
  have hinvScale := nonsing_inv_smul lam⁻¹ (inv_ne_zero hlam.ne') hdet
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · have hdiv : lam / lam ≤ Lam / lam := div_le_div_of_nonneg_right hle hlam.le
    simpa [div_self hlam.ne'] using hdiv
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right]
    calc
      1 * vecNormSq ξ = lam⁻¹ * (lam * vecNormSq ξ) := by field_simp [hlam.ne']
      _ ≤ lam⁻¹ * vecDot ξ (matVecMul A ξ) :=
        mul_le_mul_of_nonneg_left (hlower ξ) (inv_nonneg.mpr hlam.le)
  · intro ξ
    have hscale : (Lam / lam)⁻¹ = lam * Lam⁻¹ := by
      field_simp [hlam.ne', hLam.ne']
    calc
      (Lam / lam)⁻¹ * vecNormSq ξ = lam * (Lam⁻¹ * vecNormSq ξ) := by
        rw [hscale]
        ring
      _ ≤ lam * vecDot ξ (matVecMul A⁻¹ ξ) :=
        mul_le_mul_of_nonneg_left (hinv ξ) hlam.le
      _ = vecDot ξ (matVecMul (lam⁻¹ • A)⁻¹ ξ) := by
        rw [hinvScale]
        simp [smul_matVecMul, vecDot_smul_right, inv_inv]

theorem fixedNu_field_normalize {d : ℕ} {U : Set (Vec d)}
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn 1 (Lam / lam) U (lam⁻¹ • a) := by
  classical
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    have hrow : Measurable (fun x => if x ∈ U then a x i j else 0) :=
      (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i)) j
    simpa [Pi.smul_apply, smul_eq_mul] using hrow.const_mul lam⁻¹
  · intro x hx
    exact fixedNu_matrix_normalize (hEll.2 x hx)

theorem fixedNu_field_translate
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d} (z : Vec d)
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


/-- Positive viscosity makes every nonzero pure-flux response strictly positive. -/
theorem fixedNu_pure_flux_Mu_pos (Q : TriadicCube 2) {nu Lam : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu) (hEll : IsEllipticFieldOn nu Lam (cubeSet Q) a)
    {q : Vec 2} (hq : q ≠ 0) : 0 < Mu (cubeSet Q) (0, q) a := by
  let z := triadicCubeShift Q
  let U := cubeSet (originCube 2 Q.scale)
  let a0 := translateCoeffField z a
  let a1 : CoeffField 2 := nu⁻¹ • a0
  have hcube : cubeSet Q = translateSet z U :=
    cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have he0 : IsEllipticFieldOn nu Lam U a0 :=
    fixedNu_field_translate z (by simpa only [hcube] using hEll)
  have he1 : IsEllipticFieldOn 1 (Lam / nu) U a1 := fixedNu_field_normalize he0
  have hcoef : nu • a1 = a0 := by
    ext x i j
    simp only [a1, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
  have hqpos : 0 < vecNormSq q :=
    lt_of_le_of_ne (vecNormSq_nonneg q) (Ne.symm (mt vecNormSq_eq_zero hq))
  have hs : 0 < Real.sqrt nu := Real.sqrt_pos.mpr hnu
  have hlower := diag_lower_le_mu_cube he1 (loadRescale (Real.sqrt nu) (0, q))
  have hzero : (0 : Vec 2) ∈ U := by
    rw [mem_cubeSet_originCube_iff]
    intro i
    have hpow : (0 : ℝ) < (3 : ℝ) ^ Q.scale := by positivity
    simp only [Pi.zero_apply]
    constructor <;> nlinarith only [hpow]
  have hLamRatio : 0 < Lam / nu := lt_of_lt_of_le (by norm_num) (he1.2 0 hzero).2.1
  have hleft : 0 <
      (1 / 4 : ℝ) * vecNormSq (loadRescale (Real.sqrt nu) (0, q)).1 +
        (4 * (Lam / nu))⁻¹ * vecNormSq (loadRescale (Real.sqrt nu) (0, q)).2 := by
    simp only [loadRescale, smul_zero]
    rw [vecNormSq_smul]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) (vecNormSq_nonneg _))
      (mul_pos (inv_pos.mpr (mul_pos (by norm_num) hLamRatio))
        (mul_pos (sq_pos_of_pos (inv_pos.mpr hs)) hqpos))
  rw [hcube, Mu_translateSet_eq_translateCoeffField]
  change 0 < Mu U (0, q) a0
  rw [← hcoef, Mu_smul_eq he1 (measurableSet_cubeSet _) hnu]
  exact hleft.trans_le hlower

/-- Symmetry of the inverse block follows directly from the canonical
polarization defining the actual coarse matrix. -/
theorem fixedNu_inverse_hermitian (Q : TriadicCube 2) (a : CoeffField 2) :
    (coarseBlockMatrix (cubeSet Q) a).lowerRight.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial]
  change coarseBlockEntry (cubeSet Q) a (Sum.inr j) (Sum.inr i) =
    coarseBlockEntry (cubeSet Q) a (Sum.inr i) (Sum.inr j)
  unfold coarseBlockEntry
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [Sum.inr.injEq, hij, Ne.symm hij, ↓reduceDIte]
    rw [add_comm (blockBasis (Sum.inr j)) (blockBasis (Sum.inr i))]
    ring

/-- Strict positivity of the genuine inverse response block, at fixed positive viscosity. -/
theorem fixedNu_inverse_posDef (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (cubeSet Q)) :
    (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField nu sigma k)).lowerRight.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨fixedNu_inverse_hermitian Q _, ?_⟩
  intro q hq
  have he := responseFramePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q)
    nu sigma hnu hsigma k
  have hp := fixedNu_pure_flux_Mu_pos Q (div_pos hnu hsigma) he hq
  have hquad := mu_eq_half_coarseBlockMatrix_elliptic_triCube (div_pos hnu hsigma) he (0, q)
  simp only [blockVecDot, blockMatVecMul, matVecMul_zero, zero_add, vecDot_zero_left] at hquad
  have h : 0 < vecDot q (matVecMul
      (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField nu sigma k)).lowerRight q) := by
    linarith only [hquad, hp]
  simpa only [star_trivial, vecDot, matVecMul, Matrix.mulVec, dotProduct] using h

/-- The source inverse-block matrix inequality, without replacing the frame by viscosity. -/
theorem fixedNu_inverse_loewner (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (cubeSet Q)) :
    MatLoewnerLE
      (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField nu sigma k)).lowerRight
      ((sigma / nu) • (1 : Mat 2)) := by
  intro q
  have h := fixedNu_inverse_quadratic_le Q nu sigma hnu hsigma k q
  have hi : vecDot q (matVecMul ((sigma / nu) • (1 : Mat 2)) q) =
      sigma / nu * vecNormSq q := by
    simp only [smul_matVecMul, matVecMul_one, vecDot_smul_right, vecNormSq]
  rw [hi]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- The Euclidean operator-norm cap that bounds every descendant history entry. -/
theorem fixedNu_inverse_norm_le (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (cubeSet Q)) :
    Homogenization.Book.Ch02.matrixNorm
      (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField nu sigma k)).lowerRight ≤ sigma / nu := by
  have hpos := (fixedNu_inverse_posDef Q nu sigma hnu hsigma k).posSemidef
  have hid : ((sigma / nu) • (1 : Mat 2)).PosSemidef :=
    Matrix.PosSemidef.one.smul (div_nonneg hsigma.le hnu.le)
  have h := Homogenization.Book.Ch02.matrixNorm_le_of_matLoewnerLE_of_posSemidef
    hpos hid (fixedNu_inverse_loewner Q nu sigma hnu hsigma k)
  simp_rw [Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm] at h
  rw [Homogenization.Book.Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg
      (div_nonneg hsigma.le hnu.le)] at h
  exact h

end ASDExplicitGamma.Gaussian
