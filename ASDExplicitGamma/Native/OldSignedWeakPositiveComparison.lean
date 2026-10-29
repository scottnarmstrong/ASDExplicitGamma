module

public import ASDExplicitGamma.Native.OldSignedWeakTriangle
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Weak/positive norm comparisons used by the sharp pure-second feedback. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

theorem old_signed_vector_weak_le_positive (Q : TriadicCube 2)
    {f : Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2, MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hP : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => f x i)))) :
    vectorWeakHaarNorm Q f ≤ vectorPositiveHaarNorm Q f := by
  have hroot : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hbase : 0 ≤ (Real.sqrt 3)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hle : (Real.sqrt 3)⁻¹ ≤ Real.sqrt 3 := by
    exact ((inv_le_one₀ (Real.sqrt_pos.2 (by norm_num))).mpr hroot.le).trans hroot.le
  have hcoord (i : Fin 2) : dualEnergy Q (Real.sqrt 3) (fun x => f x i) ≤
      primalEnergy Q (Real.sqrt 3) (fun x => f x i) := by
    unfold dualEnergy primalEnergy
    apply add_le_add_right
    have hsum := summable_dual_increments Q hroot (hf i)
    have hterm (j : ℕ) : (Real.sqrt 3)⁻¹ ^ (j + 1) *
        energy Q (cubeIncrement Q (j + 1) (fun x => f x i)) ≤
      (Real.sqrt 3) ^ (j + 1) *
        energy Q (cubeIncrement Q (j + 1) (fun x => f x i)) := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase hle (j + 1)) (energy_nonneg Q _)
    exact hsum.tsum_le_tsum hterm (hP i)
  have hE : vectorWeakHaarEnergy Q f ≤ vectorPositiveHaarEnergy Q f := by
    simp only [vectorWeakHaarEnergy, vectorPositiveHaarEnergy]
    exact Finset.sum_le_sum fun i hi => hcoord i
  unfold vectorWeakHaarNorm vectorPositiveHaarNorm
  exact Real.sqrt_le_sqrt hE


theorem old_signed_block_snd_positive_le (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) :
    vectorPositiveHaarNorm Q (fun x => (F x).2) ≤ oldSignedBlockPositiveNorm Q F := by
  have hbot : 0 ≤ vectorPositiveHaarNorm Q (fun x => (F x).2) := Real.sqrt_nonneg _
  have hsq : (vectorPositiveHaarNorm Q (fun x => (F x).2)) ^ 2 ≤
      (oldSignedBlockPositiveNorm Q F) ^ 2 := by
    unfold oldSignedBlockPositiveNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact le_add_of_nonneg_left
      (sq_nonneg (vectorPositiveHaarNorm Q (fun x => (F x).1)))
  exact (sq_le_sq₀ hbot (Real.sqrt_nonneg _)).mp hsq

/-- Negation preserves the complete vector weak-Haar norm. -/
theorem old_signed_vector_weak_neg (Q : TriadicCube 2) (f : Vec 2 → Vec 2) :
    vectorWeakHaarNorm Q (fun x => -f x)=vectorWeakHaarNorm Q f := by
  unfold vectorWeakHaarNorm vectorWeakHaarEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change dualEnergy Q (Real.sqrt 3) (fun x => -f x i)=_
  unfold dualEnergy
  exact primalEnergy_neg Q ((Real.sqrt 3)⁻¹) (fun x => f x i)

end
end ASDExplicitGamma.Native
