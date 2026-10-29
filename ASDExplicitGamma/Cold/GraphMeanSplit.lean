module

public import ASDExplicitGamma.Cold.CoarseGramDefect
public import ASDExplicitGamma.Cold.SquareMatchedProjection

/-! # The actual graph means and the source own-cell/residual Young split -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Scalar Young inequality in exactly the source orientation. -/
theorem graph_split_scalar_young {t : ℝ} (ht : 0 < t) (x z : ℝ) :
    (x-z)^2 ≤ (1+t)*x^2+(1+1/t)*z^2 := by
  apply (mul_le_mul_iff_of_pos_left ht).mp
  field_simp
  nlinarith only [sq_nonneg (t*x+z)]

/-- The ordinary Euclidean doubled norm obeys the source parameter-t split. -/
theorem graph_split_block_young {t : ℝ} (ht : 0 < t) (P Z : BlockVec 2) :
    blockVecDot (P-Z) (P-Z) ≤ (1+t)*blockVecDot P P+(1+1/t)*blockVecDot Z Z := by
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ => graph_split_scalar_young ht (P.1 i) (Z.1 i))
  have hq := Finset.sum_le_sum (s := Finset.univ) (fun i _ => graph_split_scalar_young ht (P.2 i) (Z.2 i))
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hp hq
  unfold blockVecDot vecDot
  simp only [Prod.fst_sub,Prod.snd_sub,Pi.sub_apply,← sq]
  linarith only [hp,hq]

/-- The graph mean of the actual harmonic difference is the difference of its actual means. -/
theorem coarseGraphMean_difference (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (f v : AHarmonicFunction a (openCubeSet Q)) :
    coarseGraphMean Q (squareHarmonicDifference Q hEll f v) = coarseGraphMean Q f-coarseGraphMean Q v := by
  have hf (i : Fin 2) := (f.toH1.gradMemL2 i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hv (i : Fin 2) := (v.toH1.gradMemL2 i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hF (i : Fin 2) := (memVectorL2_matVecMul_of_isEllipticFieldOn hEll f.toH1.grad_memVectorL2).eval i
  have hV (i : Fin 2) := (memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.toH1.grad_memVectorL2).eval i
  apply Prod.ext
  · funext i
    change volumeAverage (openCubeSet Q)
      (fun x => matVecMul (a x) ((squareHarmonicDifference Q hEll f v).toH1.grad x) i) = _
    have heq : (fun x => matVecMul (a x) ((squareHarmonicDifference Q hEll f v).toH1.grad x) i) =
        (fun x => matVecMul (a x) (f.toH1.grad x) i-matVecMul (a x) (v.toH1.grad x) i) := by
      funext x
      unfold squareHarmonicDifference
      rw [AHarmonicFunction.grad_subOfIntegrable]
      simp only [Pi.sub_apply,sub_eq_add_neg,matVecMul_add,matVecMul_neg,Pi.add_apply,Pi.neg_apply]
    rw [heq]
    exact volumeAverage_sub ((hF i).integrable (by norm_num)) ((hV i).integrable (by norm_num))
  · funext i
    change volumeAverage (openCubeSet Q)
      (fun x => (squareHarmonicDifference Q hEll f v).toH1.grad x i) = _
    unfold squareHarmonicDifference
    rw [AHarmonicFunction.grad_subOfIntegrable]
    exact volumeAverage_sub (hf i) (hv i)

/-- The source graph split applies to actual own-cell and restricted-parent harmonic functions. -/
theorem own_graph_split (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam t : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (ht : 0 < t)
    (f v : AHarmonicFunction a (openCubeSet Q)) :
    blockVecDot (coarseGraphMean Q v) (coarseGraphMean Q v) ≤
      (1+t)*blockVecDot (coarseGraphMean Q f) (coarseGraphMean Q f)+
      (1+1/t)*blockVecDot (coarseGraphMean Q (squareHarmonicDifference Q hEll f v))
        (coarseGraphMean Q (squareHarmonicDifference Q hEll f v)) := by
  rw [coarseGraphMean_difference]
  have h := graph_split_block_young ht (coarseGraphMean Q f) (coarseGraphMean Q f-coarseGraphMean Q v)
  simpa only [sub_sub_cancel] using h

end ASDExplicitGamma.Cold
