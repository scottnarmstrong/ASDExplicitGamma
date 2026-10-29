module

public import ASDExplicitGamma.Inverse.AssemblyFullSensitivity
public import ASDExplicitGamma.Inverse.ShearedMatrix

/-! Exact full-pair shear comparison without a Young-inequality trace loss. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The constant-stream load map in full coordinates. -/
theorem assembly_constant_skew_mulVec (g : ℝ) (P : BlockVec 2) :
    (constantSkewMatrix g).mulVec (toFullBlockVec P) = toFullBlockVec (constantSkewLoad g P) := by
  unfold constantSkewMatrix
  rw [← toFullBlockVec_blockMatVecMul]
  congr 1
  ext i <;> fin_cases i <;> simp [blockMatVecMul,constantSkewLoad,matVecMul,
    Fin.sum_univ_two,responsePlanarJ] <;> ring

/-- A constant stream shift acts on the paired load exactly. -/
theorem assembly_constant_skew_quadratic (g : ℝ) (A : BlockMat 2) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (constantSkewCongruence g A) P) =
      blockVecDot (constantSkewLoad g P) (blockMatVecMul A (constantSkewLoad g P)) := by
  rw [← dotProduct_toFullBlockVec,toFullBlockVec_blockMatVecMul]
  simp only [constantSkewCongruence,toFullBlockMat_ofFullBlockMat,← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,assembly_constant_skew_mulVec]
  rw [← toFullBlockVec_blockMatVecMul,dotProduct_toFullBlockVec]

/-- Centered paired-load domination survives the exact physical shear. -/
theorem assembly_shear_pair_domination (A B : BlockMat 2) (c g : ℝ)
    (hAB : ∀ P : BlockVec 2, blockVecDot P (blockMatVecMul A P) ≤
      c*blockVecDot P (blockMatVecMul B P)) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (constantSkewCongruence g A) P) ≤
      c*blockVecDot P (blockMatVecMul (constantSkewCongruence g B) P) := by
  rw [assembly_constant_skew_quadratic,assembly_constant_skew_quadratic]
  exact hAB _

/-- True framing changes the physical stream shear parameter from g to g/σ. -/
theorem assembly_frame_constant_skew (σ g : ℝ) (hσ : 0 < σ) (A : BlockMat 2) :
    toFullBlockMat (frameMatrix σ (constantSkewCongruence g A)) =
      (constantSkewMatrix (g/σ)).transpose*toFullBlockMat (frameMatrix σ A)*
        constantSkewMatrix (g/σ) := by
  let D := frameDiagonal σ
  let R := constantSkewMatrix g
  let S := constantSkewMatrix (g/σ)
  have hD : D.transpose=D := by simp only [D,frameDiagonal,Matrix.diagonal_transpose]
  have hcomm : R*D=D*S := by
    have hs := (Real.sqrt_pos.mpr hσ).ne'
    have hs2 := Real.sq_sqrt hσ.le
    ext α β
    cases α <;> cases β
    all_goals
      simp [R,D,S,frameDiagonal,constantSkewMatrix,toFullBlockMat,Matrix.mul_apply,
        Matrix.diagonal,Matrix.smul_apply]
    all_goals field_simp [hσ.ne',hs]
    all_goals rw [hs2]
  rw [toFullBlockMat_frameMatrix_eq_diagonal_congruence σ _ hσ,
    constantSkewCongruence,toFullBlockMat_ofFullBlockMat,
    toFullBlockMat_frameMatrix_eq_diagonal_congruence σ A hσ]
  change D*(R.transpose*toFullBlockMat A*R)*D = S.transpose*(D*toFullBlockMat A*D)*S
  calc
    _ = (R*D).transpose*toFullBlockMat A*(R*D) := by
      rw [Matrix.transpose_mul,hD]
      simp only [Matrix.mul_assoc]
    _ = (D*S).transpose*toFullBlockMat A*(D*S) := by rw [hcomm]
    _ = _ := by rw [Matrix.transpose_mul,hD]; simp only [Matrix.mul_assoc]

/-- Exact normalized trace after shear; there is no extra factor two on the
identity-cell baseline or on its squared-average coefficient. -/
theorem assembly_shear_trace_domination (A B : BlockMat 2) (c σ g : ℝ) (hσ : 0 < σ)
    (hAB : ∀ P : BlockVec 2, blockVecDot P (blockMatVecMul A P) ≤
      c*blockVecDot P (blockMatVecMul B P)) :
    Matrix.trace (toFullBlockMat (frameMatrix σ (constantSkewCongruence g A)))/4 ≤
      c*(Matrix.trace ((constantSkewMatrix (g/σ)).transpose*
        toFullBlockMat (frameMatrix σ B)*constantSkewMatrix (g/σ))/4) := by
  have hh := full_response_frame_trace_le_of_pair_quadratic σ c hσ
    (constantSkewCongruence g A) (constantSkewCongruence g B)
    (assembly_shear_pair_domination A B c g hAB)
  rwa [assembly_frame_constant_skew σ g hσ B] at hh

end
end ASDExplicitGamma.Inverse
