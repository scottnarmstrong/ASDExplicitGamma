module

public import ASDExplicitGamma.Native.OldSignedFlatJointL2
public import ASDExplicitGamma.Native.OldSignedCenteredPositive

/-! The affine cell-mean loss is paid by the already-proved flat oscillations. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic
noncomputable section

/-- Full block L2 energy is below its genuine positive Haar energy. -/
theorem old_signed_block_l2_le_positive (Q : TriadicCube 2) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (hfst : ∀ i,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => (F x).1 i))))
    (hsnd : ∀ i,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => (F x).2 i)))) :
    oldSignedBlockL2Energy Q F≤oldSignedBlockPositiveNorm Q F^2 := by
  have h1 := vectorL2_le_vectorPositiveHaar Q (fun x => (F x).1)
    (fun i => memLp_normalized_of_memL2On ((memVectorL2_fst_of_memBlockL2 hF).eval i)) hfst
  have h2 := vectorL2_le_vectorPositiveHaar Q (fun x => (F x).2)
    (fun i => memLp_normalized_of_memL2On ((memVectorL2_snd_of_memBlockL2 hF).eval i)) hsnd
  have hs1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  have hs2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => energy_nonneg Q _))] at hs1 hs2
  rw [oldSignedBlockPositiveNorm,Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact add_le_add hs1 hs2

/-- The complete cell mean profile has its exact nonnegative covariance
sum as square. -/
theorem old_signed_flat_mean_size_sq (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    oldSignedFlatMeanSize Q U b L plus^2=
      ∑' n : whiteBasisIndex,∑ i : Fin 2,
        blockVecDot (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i))
          (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)) := by
  apply Real.sq_sqrt
  apply tsum_nonneg
  intro n
  exact Finset.sum_nonneg (fun i _ => add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))

end
end ASDExplicitGamma.Native
