module

public import ASDExplicitGamma.Inverse.HistoryDefectMatrix
public import ASDExplicitGamma.Inverse.ClippedMatrixResponseScalar

/-! The sharp reflected energy product lower bound uses only the genuine
variational pairing inequalities; no inverse-matrix identity is assumed. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization

/-- Exact quadratic parallelogram for a doubled response matrix. -/
theorem clipped_block_energy_parallelogram (C : BlockMat 2) (P R : BlockVec 2) (s : ℝ) :
    blockVecDot (s • P+R) (blockMatVecMul C (s • P+R))+
      blockVecDot (s • P+(-1:ℝ) • R) (blockMatVecMul C (s • P+(-1:ℝ) • R)) =
    2*s^2*blockVecDot P (blockMatVecMul C P)+2*blockVecDot R (blockMatVecMul C R) := by
  simp only [blockMatVecMul_add,blockMatVecMul_smul,blockVecDot_add_left,blockVecDot_add_right,
    blockVecDot_smul_left,blockVecDot_smul_right]
  ring

private theorem paired_cross_identity (p q : Vec 2) (s : ℝ) :
    2*vecDot (s • p+q) (s • q+p)-2*vecDot (s • p-q) (s • q-p) =
      4*s*(vecDot p p+vecDot q q) := by
  simp only [vecDot,Fin.sum_univ_two,Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  ring

/-- The C±R variational lower bounds imply the reflected-energy product bound
for every loading, including zero. This proves the needed step directly from
admissibility and avoids assuming coarse self-duality. -/
theorem clipped_block_energy_product (C : BlockMat 2)
    (hp : ∀ p q : Vec 2, 2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (hn : ∀ p q : Vec 2, -2*vecDot p q ≤ blockVecDot (p,q) (blockMatVecMul C (p,q)))
    (P : BlockVec 2) :
    (blockVecDot P P)^2 ≤ blockVecDot P (blockMatVecMul C P)*
      blockVecDot (P.2,P.1) (blockMatVecMul C (P.2,P.1)) := by
  apply clipped_energy_product_lower
  intro s
  let R : BlockVec 2 := (P.2,P.1)
  have h1 := hp (s • P+R).1 (s • P+R).2
  have h2 := hn (s • P+(-1:ℝ) • R).1 (s • P+(-1:ℝ) • R).2
  have he := clipped_block_energy_parallelogram C P R s
  have hx : 2*vecDot (s • P+R).1 (s • P+R).2+
      -2*vecDot (s • P+(-1:ℝ) • R).1 (s • P+(-1:ℝ) • R).2 = 4*s*blockVecDot P P := by
    change 2*vecDot (s • P.1+P.2) (s • P.2+P.1)+
      -2*vecDot (s • P.1+(-1:ℝ) • P.2) (s • P.2+(-1:ℝ) • P.1) = _
    simpa only [neg_one_smul,← sub_eq_add_neg,blockVecDot,sub_eq_add_neg,neg_mul] using
      paired_cross_identity P.1 P.2 s
  change 0 ≤ blockVecDot P (blockMatVecMul C P)*(s*s)-2*blockVecDot P P*s+
    blockVecDot R (blockMatVecMul C R)
  have hsum := add_le_add h1 h2
  change _ ≤ blockVecDot (s • P+R) (blockMatVecMul C (s • P+R))+
    blockVecDot (s • P+(-1:ℝ) • R) (blockMatVecMul C (s • P+(-1:ℝ) • R)) at hsum
  rw [he,hx] at hsum
  nlinarith only [hsum]

end ASDExplicitGamma.Inverse
