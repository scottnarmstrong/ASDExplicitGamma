module

public import ASDExplicitGamma.Variational.CubeFrameResponse
public import Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.MatrixTools

/-! The actual reflected symmetric operator defect, and its trace domination. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization

/-- H=(C+RCR)/2-I, with C the already framed doubled coarse matrix. -/
noncomputable def historyDefectMatrix (C : BlockMat 2) : FullBlockMat 2 :=
  (1/2 : ℝ) • (toFullBlockMat C+toFullBlockMat (blockReflect C)) - 1

/-- Split into the +1 and -1 eigenspaces of the block reflection. -/
theorem history_defect_quadratic_split (C : BlockMat 2) (P : BlockVec 2) :
    dotProduct (toFullBlockVec P) ((historyDefectMatrix C).mulVec (toFullBlockVec P)) =
      blockVecDot ((1/2:ℝ) • (P.1+P.2),(1/2:ℝ) • (P.1+P.2))
        (blockMatVecMul C ((1/2:ℝ) • (P.1+P.2),(1/2:ℝ) • (P.1+P.2)))+
      blockVecDot ((1/2:ℝ) • (P.1-P.2),-((1/2:ℝ) • (P.1-P.2)))
        (blockMatVecMul C ((1/2:ℝ) • (P.1-P.2),-((1/2:ℝ) • (P.1-P.2))))-
      blockVecDot P P := by
  rcases P with ⟨p,q⟩
  norm_num [historyDefectMatrix,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,
    toFullBlockVec,toFullBlockMat,blockReflect,blockVecDot,blockMatVecMul,vecDot,matVecMul,
    Pi.smul_apply,Matrix.smul_apply,Pi.add_apply,Pi.sub_apply,Matrix.add_apply,Matrix.sub_apply,
    Matrix.one_apply,smul_eq_mul]
  ring

/-- Pairing lower bounds imply positivity of the reflected defect. -/
theorem history_defect_quadratic_nonneg (C : BlockMat 2)
    (hp : ∀ p q : Vec 2, 2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (hn : ∀ p q : Vec 2, -2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (P : BlockVec 2) :
    0 ≤ dotProduct (toFullBlockVec P) ((historyDefectMatrix C).mulVec (toFullBlockVec P)) := by
  rw [history_defect_quadratic_split]
  let x : Vec 2 := (1/2:ℝ) • (P.1+P.2)
  let y : Vec 2 := (1/2:ℝ) • (P.1-P.2)
  have h1 := hp x x
  have h2 := hn y (-y)
  have hid : 2*vecDot x x-2*vecDot y (-y) = blockVecDot P P := by
    simp only [x,y,blockVecDot,vecDot,Fin.sum_univ_two,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,
      Pi.neg_apply,smul_eq_mul]
    ring
  change 0 ≤ blockVecDot (x,x) (blockMatVecMul C (x,x))+
    blockVecDot (y,-y) (blockMatVecMul C (y,-y))-blockVecDot P P
  linarith only [h1,h2,hid]

theorem history_defect_posSemidef (C : BlockMat 2) (hC : IsSymmetricBlockMat C)
    (hp : ∀ p q : Vec 2, 2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (hn : ∀ p q : Vec 2, -2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q))) :
    (historyDefectMatrix C).PosSemidef := by
  have hC' := isSymm_toFullBlockMat_of_isSymmetricBlockMat hC
  have hR' := isSymm_toFullBlockMat_of_isSymmetricBlockMat (isSymmetricBlockMat_blockReflect hC)
  have hSymm : (historyDefectMatrix C).IsSymm := ((hC'.add hR').smul (1/2:ℝ)).sub Matrix.isSymm_one
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (by simpa [Matrix.IsHermitian,Matrix.IsSymm] using hSymm)
  intro v
  have h := history_defect_quadratic_nonneg C hp hn (ofFullBlockVec v)
  simpa only [toFullBlockVec_ofFullBlockVec,star_trivial] using h

/-- Its trace is exactly the frozen four-load defect in the same frame. -/
theorem history_defect_trace (sigma : ℝ) (A : BlockMat 2) :
    Book.Ch02.fullBlockTrace (historyDefectMatrix (Variational.frameMatrix sigma A)) =
      sigma⁻¹*Matrix.trace A.upperLeft+sigma*Matrix.trace A.lowerRight-4 := by
  norm_num [Book.Ch02.fullBlockTrace,historyDefectMatrix,Variational.frameMatrix,Matrix.trace,
    Fintype.sum_sum_type,Fin.sum_univ_two,toFullBlockMat,blockReflect,Matrix.smul_apply,
    Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply,smul_eq_mul]
  ring

end ASDExplicitGamma.Inverse
