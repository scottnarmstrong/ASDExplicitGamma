module

public import ASDExplicitGamma.Variational.TraceDefect

@[expose] public section

namespace ASDExplicitGamma.Response

open Homogenization

noncomputable section

/-! The two dimensional block algebra behind the fixed-frame shear. -/

/-- The positive quarter turn on the planar vector carrier. -/
def responsePlanarJ : Mat 2 := !![0, -1; 1, 0]

theorem responsePlanarJ_vecNormSq (x : Vec 2) :
    vecNormSq (matVecMul responsePlanarJ x) = vecNormSq x := by
  simp [vecNormSq, vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two]
  ring

/-- A planar coefficient with symmetric part `ν I` and skew part `κ J`. -/
def responsePlanarCoefficient (ν κ : ℝ) : Mat 2 :=
  ν • (1 : Mat 2) + κ • responsePlanarJ

/-- Frame-scaled pointwise quadratic energy. -/
def responseFrameEnergyDensity (ν σ κ : ℝ) (X : BlockVec 2) : ℝ :=
  (ν / σ) * vecNormSq X.1 + (σ / ν) *
    vecNormSq (X.2 - (κ / σ) • matVecMul responsePlanarJ X.1)

/-- The nilpotent correction `C_H X` in the physical frame. -/
def responseShearCorrection (σ η : ℝ) (X : BlockVec 2) : BlockVec 2 :=
  (0, -((η / σ) • matVecMul responsePlanarJ X.1))

/-- The affine shear `I + C_H` in the physical frame. -/
def responseShear (σ η : ℝ) (X : BlockVec 2) : BlockVec 2 :=
  X + responseShearCorrection σ η X

private theorem responseShear_flux_identity (σ κ η : ℝ) (X : BlockVec 2) :
    (responseShear σ η X).2 - ((κ / σ) • matVecMul responsePlanarJ
        (responseShear σ η X).1) =
      X.2 - (((κ + η) / σ) • matVecMul responsePlanarJ X.1) := by
  ext i
  simp [responseShear, responseShearCorrection]
  ring

/-- Exact pointwise factorization of the perturbed energy; only the frame
factor `σ⁻¹` appears in the shear. -/
theorem responseFrameEnergyDensity_shear (ν σ κ η : ℝ) (X : BlockVec 2) :
    responseFrameEnergyDensity ν σ (κ + η) X =
      responseFrameEnergyDensity ν σ κ (responseShear σ η X) := by
  rw [responseFrameEnergyDensity, responseFrameEnergyDensity,
    responseShear_flux_identity]
  simp [responseShear, responseShearCorrection]

/-- The physical shear is bounded by `|η|/ν` in the fixed coefficient's
frame energy norm. -/
theorem responseFrameEnergyDensity_shearCorrection_le
    (ν σ κ η : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (X : BlockVec 2) :
    responseFrameEnergyDensity ν σ κ (responseShearCorrection σ η X) ≤
      (|η| / ν) ^ 2 * responseFrameEnergyDensity ν σ κ X := by
  rcases X with ⟨u, v⟩
  have hJ := responsePlanarJ_vecNormSq u
  have hres : 0 ≤ (σ / ν) *
      vecNormSq (v - (κ / σ) • matVecMul responsePlanarJ u) := by
    exact mul_nonneg (div_nonneg hσ.le hν.le) (vecNormSq_nonneg _)
  have hleft : responseFrameEnergyDensity ν σ κ
      (responseShearCorrection σ η (u, v)) =
        (σ / ν) * (η / σ) ^ 2 * vecNormSq u := by
    rw [responseFrameEnergyDensity, responseShearCorrection]
    simp only [matVecMul_zero, sub_zero, smul_zero]
    rw [show vecNormSq (0 : Vec 2) = 0 by simp [vecNormSq, vecDot]]
    rw [← neg_smul]
    rw [vecNormSq_smul, hJ]
    ring
  have hcoeff : (σ / ν) * (η / σ) ^ 2 = (η / ν) ^ 2 * (ν / σ) := by
    field_simp [hν.ne', hσ.ne']
  have hnormv : vecNormSq u ≥ 0 := vecNormSq_nonneg u
  have hratio : (|η| / ν) ^ 2 = (η / ν) ^ 2 := by
    rw [div_pow, sq_abs]
    ring
  have hrest' : 0 ≤ (η / ν) ^ 2 *
      ((σ / ν) * vecNormSq (v - (κ / σ) • matVecMul responsePlanarJ u)) :=
    mul_nonneg (sq_nonneg _) hres
  rw [hleft, hcoeff, hratio, responseFrameEnergyDensity]
  nlinarith [hnormv, hrest']

private theorem responsePlanarCoefficient_symmPart (ν κ : ℝ) :
    symmPart (responsePlanarCoefficient ν κ) = ν • (1 : Mat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [responsePlanarCoefficient, responsePlanarJ, symmPart,
      Matrix.smul_apply, smul_eq_mul]

private theorem responsePlanarCoefficient_skewPart (ν κ : ℝ) :
    skewPart (responsePlanarCoefficient ν κ) = κ • responsePlanarJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [responsePlanarCoefficient, responsePlanarJ, skewPart,
      Matrix.smul_apply, smul_eq_mul]
  all_goals ring

private theorem responsePlanarSymm_inv (ν : ℝ) (hν : ν ≠ 0) :
    (ν • (1 : Mat 2))⁻¹ = ν⁻¹ • (1 : Mat 2) := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  <;> field_simp

/-- The explicit inverse of the planar coefficient `ν I + κ J`. -/
def responsePlanarCoefficientInverse (ν κ : ℝ) : Mat 2 :=
  !![ν / (ν ^ 2 + κ ^ 2), κ / (ν ^ 2 + κ ^ 2);
    -κ / (ν ^ 2 + κ ^ 2), ν / (ν ^ 2 + κ ^ 2)]

theorem responsePlanarCoefficient_inv (ν κ : ℝ) (hν : 0 < ν) :
    (responsePlanarCoefficient ν κ)⁻¹ = responsePlanarCoefficientInverse ν κ := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarCoefficientInverse,
      responsePlanarJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [ne_of_gt (show 0 < ν ^ 2 + κ ^ 2 by positivity)] <;> ring

theorem responsePlanarCoefficient_quadratic (ν κ : ℝ) (x : Vec 2) :
    vecDot x (matVecMul (responsePlanarCoefficient ν κ) x) =
      ν * vecNormSq x := by
  simp [responsePlanarCoefficient, responsePlanarJ, vecDot, vecNormSq,
    matVecMul, Fin.sum_univ_two]
  ring

theorem responsePlanarCoefficientInverse_quadratic (ν κ : ℝ) (x : Vec 2) :
    vecDot x (matVecMul (responsePlanarCoefficientInverse ν κ) x) =
      (ν / (ν ^ 2 + κ ^ 2)) * vecNormSq x := by
  simp [responsePlanarCoefficientInverse, vecDot, vecNormSq, matVecMul,
    Fin.sum_univ_two]
  ring

/-- Quantitative ellipticity of the two dimensional skew perturbation, with
the symmetric ellipticity constant still equal to `ν`. -/
theorem responsePlanarCoefficient_isElliptic (ν M κ : ℝ)
    (hν : 0 < ν) (hκ : |κ| ≤ M) :
    IsEllipticMatrix ν ((ν ^ 2 + M ^ 2) / ν)
      (responsePlanarCoefficient ν κ) := by
  have hM : 0 ≤ M := le_trans (abs_nonneg κ) hκ
  have hLam : ν ≤ (ν ^ 2 + M ^ 2) / ν := by
    rw [le_div_iff₀ hν]
    nlinarith [sq_nonneg M]
  have hκsq : κ ^ 2 ≤ M ^ 2 := by
    simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg κ) hM).2 hκ
  have hden : ν ^ 2 + κ ^ 2 ≤ ν ^ 2 + M ^ 2 := by
    nlinarith
  have hden_pos : 0 < ν ^ 2 + κ ^ 2 := by positivity
  have hInvCoeff : ((ν ^ 2 + M ^ 2) / ν)⁻¹ =
      ν / (ν ^ 2 + M ^ 2) := by
    field_simp [ne_of_gt hν, ne_of_gt (show 0 < ν ^ 2 + M ^ 2 by positivity)]
  have hInvBound : ν / (ν ^ 2 + M ^ 2) ≤ ν / (ν ^ 2 + κ ^ 2) :=
    div_le_div_of_nonneg_left hν.le hden_pos hden
  refine ⟨hν, hLam, ?_, ?_⟩
  · intro x
    rw [responsePlanarCoefficient_quadratic]
  · intro x
    rw [responsePlanarCoefficient_inv ν κ hν,
      responsePlanarCoefficientInverse_quadratic, hInvCoeff]
    exact mul_le_mul_of_nonneg_right hInvBound (vecNormSq_nonneg x)

private theorem response_matVecMul_one (x : Vec 2) :
    matVecMul (1 : Mat 2) x = x := by
  ext i
  simp [matVecMul, Matrix.one_apply]

private theorem response_vecDot_smul_right (x y : Vec 2) (c : ℝ) :
    vecDot x (c • y) = c * vecDot x y := by
  simp [vecDot, Pi.smul_apply, Fin.sum_univ_two]
  ring

/-- The pointwise energy is the quadratic form of CoarseGraining's doubled
coefficient matrix, conjugated by the diagonal frame. -/
theorem responseFrameEnergyDensity_eq_blockMatrix (ν σ κ : ℝ) (hν : ν ≠ 0)
    (hσ : 0 < σ) (X : BlockVec 2) :
    responseFrameEnergyDensity ν σ κ X =
      blockVecDot X (blockMatVecMul
        (ASDExplicitGamma.Variational.frameMatrix σ
          (blockMatrixOfCoeff (responsePlanarCoefficient ν κ))) X) := by
  let s : ℝ := (Real.sqrt σ)⁻¹
  have hs : Real.sqrt σ ≠ 0 := Real.sqrt_ne_zero'.mpr hσ
  have hs2 : s ^ 2 = σ⁻¹ := by
    dsimp [s]
    rw [inv_pow, Real.sq_sqrt hσ.le]
  have hsinv : s⁻¹ = Real.sqrt σ := by
    dsimp [s]
    exact inv_inv (Real.sqrt σ)
  have hsinv2 : (s⁻¹) ^ 2 = σ := by
    rw [hsinv, Real.sq_sqrt hσ.le]
  have hs0 : s ≠ 0 := inv_ne_zero hs
  have hσinv : σ⁻¹ = s ^ 2 := hs2.symm
  have hraw := blockMatrixOfCoeff_quadratic_eq
    (responsePlanarCoefficient ν κ) (s • X.1) (s⁻¹ • X.2)
  rw [responsePlanarCoefficient_symmPart, responsePlanarCoefficient_skewPart,
    responsePlanarSymm_inv ν hν] at hraw
  have hframe : blockVecDot X
      (blockMatVecMul (ASDExplicitGamma.Variational.frameMatrix σ
        (blockMatrixOfCoeff (responsePlanarCoefficient ν κ))) X) =
      blockVecDot (s • X.1, s⁻¹ • X.2)
        (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient ν κ))
          (s • X.1, s⁻¹ • X.2)) := by
    simp only [ASDExplicitGamma.Variational.frameMatrix, blockVecDot,
      blockMatVecMul, smul_matVecMul, matVecMul_smul,
      vecDot_add_right, vecDot_smul_left, vecDot_smul_right]
    rw [hσinv, ← hsinv2]
    field_simp [hs0]
  rw [hframe, hraw]
  have hshift : s⁻¹ • X.2 - matVecMul (κ • responsePlanarJ) (s • X.1) =
      s⁻¹ • (X.2 - (κ / σ) • matVecMul responsePlanarJ X.1) := by
    rw [smul_matVecMul, matVecMul_smul]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply]
    rw [div_eq_mul_inv, hσinv]
    simp only [smul_smul]
    have hcoeff : s⁻¹ * (κ * s ^ 2) = κ * s := by
      field_simp [hs0]
    rw [smul_sub, smul_smul, hcoeff]
  rw [responseFrameEnergyDensity, hshift]
  simp only [smul_matVecMul, response_matVecMul_one, smul_smul]
  rw [vecDot_smul_left, vecDot_smul_right,
    vecDot_smul_left, vecDot_smul_right]
  simp only [vecNormSq]
  simp only [div_eq_mul_inv]
  rw [hσinv, ← hsinv2]
  ring

/-- The same frame energy is the direct block quadratic for the coefficient
`(ν I + κ J) / σ`. -/
theorem responseFrameEnergyDensity_eq_scaledCoefficientBlock (ν σ κ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (X : BlockVec 2) :
    responseFrameEnergyDensity ν σ κ X =
      blockVecDot X (blockMatVecMul
        (blockMatrixOfCoeff
          (responsePlanarCoefficient (ν / σ) (κ / σ))) X) := by
  have hνσ : ν / σ ≠ 0 := ne_of_gt (div_pos hν hσ)
  rcases X with ⟨u, v⟩
  rw [responseFrameEnergyDensity, blockMatrixOfCoeff_quadratic_eq,
    responsePlanarCoefficient_symmPart,
    responsePlanarCoefficient_skewPart,
    responsePlanarSymm_inv (ν / σ) hνσ]
  simp only [smul_matVecMul, response_matVecMul_one]
  rw [response_vecDot_smul_right, response_vecDot_smul_right]
  simp only [vecNormSq]
  field_simp [hν.ne', hσ.ne']

end

end ASDExplicitGamma.Response
