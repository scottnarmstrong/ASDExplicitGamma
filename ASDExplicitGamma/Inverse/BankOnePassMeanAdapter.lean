module

public import ASDExplicitGamma.Inverse.BankOnePassHeat
public import ASDExplicitGamma.Inverse.ClippedMatrixEvent
public import ASDExplicitGamma.Cold.NativeTrace

/-! Physical lower-right trace means, starting native caps, and inverse-only clipping. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Variational
open scoped Matrix.Norms.Elementwise

theorem bank_completed_inverse_trace_mean_eq (q : ℤ) (M : ABKModel 2) (m : ℤ) (σ : ℝ) :
    bankCompletedInverseTraceMean q M m σ = Matrix.trace
      (frameMatrix σ (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
        (cubeSet (originCube 2 q)))).lowerRight := by
  have hi := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_frameMatrix_entry M m (originCube 2 q) σ (Sum.inr i) (Sum.inr i))
  have hh : (∫ a : RegCoeffField 2, bankInverseTrace q a.toFun σ
      ∂(Cutoff.coefficientCutoffLaw M m)) = Matrix.trace
        (frameMatrix σ (Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m)
          (cubeSet (originCube 2 q)))).lowerRight := by
    change (∫ a : RegCoeffField 2, ∑ i : Fin 2,
      blockMatEntry (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 q)) a.toFun))
        (Sum.inr i) (Sum.inr i) ∂(Cutoff.coefficientCutoffLaw M m)) = _
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_frameMatrix_entry M m (originCube 2 q) σ (Sum.inr i) (Sum.inr i))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_frameMatrix_entry M m _ σ (Sum.inr i) (Sum.inr i)
  change Integrable (fun a : RegCoeffField 2 => bankInverseTrace q a.toFun σ)
    (Cutoff.coefficientCutoffLaw M m) at hi
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hh hi
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable
    hi.aestronglyMeasurable] at hh
  exact hh

theorem bank_completed_inverse_trace_mean_rescale (q : ℤ) (M : ABKModel 2) (m : ℤ)
    (σ σ' : ℝ) (hσ : σ ≠ 0) :
    bankCompletedInverseTraceMean q M m σ' =
      (σ'/σ)*bankCompletedInverseTraceMean q M m σ := by
  rw [bank_completed_inverse_trace_mean_eq,bank_completed_inverse_trace_mean_eq]
  simp only [frameMatrix,Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply,
    Matrix.smul_apply,smul_eq_mul]
  field_simp [hσ]

/-- The ordinary native mean supplies the starting lower-right trace cap,
using the true-frame lower bound on the other block. -/
theorem bank_completed_inverse_trace_mean_start (M : ABKModel 2) (h : ℝ) (k : ℤ) (hstate : nativeInductionState M h k) :
    bankCompletedInverseTraceMean k M k (Annealed.sigmaBar M k:ℝ) ≤ 2+(3/50:ℝ)*theta M := by
  have ht : 0 ≤ theta M := by
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hm := hstate.1
  have hh := Cold.coldNativeMean_zero_le (mul_nonneg (by norm_num : (0:ℝ)≤3/50) ht) hm
  have htr : (∫ a : RegCoeffField 2,
      traceDefect (translateSet (0:Vec 2) (cubeSet (originCube 2 k))) a.toFun
        (Annealed.sigmaBar M k:ℝ) ∂(Cutoff.coefficientCutoffLaw M k)) ≤ (3/50:ℝ)*theta M := by
    rw [translateSet_zero,Cutoff.coefficientCutoffLaw_eq_map]
    rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu k).aemeasurable
      (integrable_traceDefect_cutoffLaw M k (originCube 2 k)
        (Annealed.sigmaBar M k:ℝ)).aestronglyMeasurable]
    simpa only [Cold.coldNativeMean,Cold.coldNativeTrace,Int.natCast_zero,add_zero,
      cutoffTraceDefect] using hh
  obtain ⟨a,b,_,_,_,hb,hframe⟩ := exists_trueFrame_mean_bounds M k k _ htr
  rw [bank_completed_inverse_trace_mean_eq]
  have hf := (hframe 0).1
  rw [translateSet_zero] at hf
  rw [hf]
  simp only [Book.Ch02.blockDiag,Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply,
    Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,ite_true]
  linarith only [hb]

/-- A directional trace mean cap yields exactly the clipped inverse-block
quadratic cap, on every physical translate and for every clipping threshold. -/
theorem bank_clipped_inverse_mean_of_trace (M : ABKModel 2) (n : ℤ) (c : ℝ)
    (htrace : bankCompletedInverseTraceMean (n-40) M n (Annealed.sigmaBar M n:ℝ) ≤ 2*c)
    (U : TriadicCube 2) (hU : U.scale=n-40) (tau : ℝ) (v : Vec 2) :
    fullMatrixQuadratic (toFullBlockVec (0,v))
      (∫ ω, clippedCellMatrix M n U tau ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        c*dotProduct v v := by
  have hclip := clipped_matrix_integral_quadratic_le (Cutoff.cutoffSampleLaw M).toMeasure
    (clippedSourceMatrix M n U) (clipped_source_integrable M n U)
    (Filter.Eventually.of_forall fun ω v => clipped_source_quadratic_nonneg M n U ω v)
    _ (clipped_cell_good_event_measurable M n U tau) (toFullBlockVec (0,v))
  apply hclip.trans
  rw [clipped_source_integral, fullMatrixQuadratic_block]
  obtain ⟨a,b,_,_,hf⟩ := exists_trueFrame_mean_scalars M n (n-40)
  have hb : b ≤ c := by
    rw [bank_completed_inverse_trace_mean_eq] at htrace
    have hh := hf 0
    rw [translateSet_zero] at hh
    rw [hh] at htrace
    simp only [Book.Ch02.blockDiag,Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply,
      Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,ite_true] at htrace
    linarith only [htrace]
  have he : translateSet (triadicCubeShift U) (cubeSet (originCube 2 (n-40))) = cubeSet U := by
    rw [← hU,← cubeSet_eq_translateSet_originCube_of_triadicCube U]
  have hframe := hf (triadicCubeShift U)
  rw [he] at hframe
  rw [hframe]
  have heq : blockVecDot (0,v)
      (blockMatVecMul (Book.Ch02.blockDiag (a • (1:Mat 2)) (b • (1:Mat 2))) (0,v)) =
        b*dotProduct v v := by
    simp [blockVecDot,blockMatVecMul,Book.Ch02.blockDiag,vecDot,matVecMul,
      dotProduct,Fin.sum_univ_two]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))

end ASDExplicitGamma.Inverse
