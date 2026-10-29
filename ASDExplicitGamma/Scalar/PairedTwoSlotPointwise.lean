module

public import ASDExplicitGamma.Variational.LemmaVEnvelope

/-! Pointwise action of the planar doubled coefficient used by the two-slot bound. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response

noncomputable section

theorem planar_symmPart (ν κ : ℝ) :
    symmPart (responsePlanarCoefficient ν κ) = ν • (1 : Mat 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symmPart, responsePlanarCoefficient, responsePlanarJ]

theorem planar_skewPart (ν κ : ℝ) :
    skewPart (responsePlanarCoefficient ν κ) = κ • responsePlanarJ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skewPart, responsePlanarCoefficient, responsePlanarJ]
  ring

/-- Lower image of the doubled planar coefficient. -/
theorem planar_block_lower {ν κ : ℝ} (hν : 0 < ν) (p q : Vec 2) :
    (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient ν κ)) (p, q)).2 =
      ν⁻¹ • (q - κ • matVecMul responsePlanarJ p) := by
  rw [blockMatVecMul_blockMatrixOfCoeff_snd, planar_symmPart, planar_skewPart]
  have hinv : (ν • (1 : Mat 2))⁻¹ = ν⁻¹ • (1 : Mat 2) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hν.ne']
  rw [hinv]
  ext i
  fin_cases i <;> simp [matVecMul, Matrix.smul_apply, Matrix.one_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, responsePlanarJ] <;> ring

/-- Upper image of the doubled planar coefficient. -/
theorem planar_block_upper {ν κ : ℝ} (hν : 0 < ν) (p q : Vec 2) :
    (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient ν κ)) (p, q)).1 =
      ν • p + κ • matVecMul responsePlanarJ
        (ν⁻¹ • (q - κ • matVecMul responsePlanarJ p)) := by
  rw [blockMatVecMul_blockMatrixOfCoeff_fst, planar_symmPart, planar_skewPart]
  have hinv : (ν • (1 : Mat 2))⁻¹ = ν⁻¹ • (1 : Mat 2) := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hν.ne']
  rw [hinv]
  ext i
  fin_cases i <;> simp [matVecMul, Matrix.smul_apply, Matrix.one_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two, responsePlanarJ] <;> ring

end

end ASDExplicitGamma.Scalar
