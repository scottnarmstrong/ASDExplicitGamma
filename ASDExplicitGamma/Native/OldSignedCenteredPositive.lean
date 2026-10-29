module

public import ASDExplicitGamma.Native.OldSignedFlatMeans
public import ASDExplicitGamma.Triadic.DiagBessel
public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy

/-! Exact affine centering of the OLD positive norms. The root mean is
subtracted algebraically; all complete positive-depth increments are retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Exact zero positive energy, from quadratic scalar homogeneity. -/
theorem old_signed_primal_zero (Q : TriadicCube 2) (q : ℝ) :
    primalEnergy Q q (fun _ : Vec 2 => (0:ℝ))=0 := by
  simpa only [zero_mul,zero_pow (by decide : 2≠0)] using
    sensitivity_primalEnergy_smul Q q (fun _ : Vec 2 => (0:ℝ)) 0

/-- Removing the actual mean subtracts exactly its square from positive
energy; no martingale tail is truncated. -/
theorem old_signed_primal_sub_mean (Q : TriadicCube 2) (q : ℝ) (f : Vec 2 → ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    primalEnergy Q q (fun x => f x-cubeAverage Q f)=primalEnergy Q q f-cubeAverage Q f^2 := by
  simpa only [dualEnergy,inv_inv] using diagDualEnergy_sub_mean Q q⁻¹ hf

/-- The block-positive norm square is the literal sum of all four
positive scalar energies in the same cell. -/
theorem old_signed_block_positive_norm_sq (Q : TriadicCube 2) (F : Vec 2 → BlockVec 2) :
    oldSignedBlockPositiveNorm Q F^2=
      (∑ i : Fin 2,primalEnergy Q (Real.sqrt 3) (fun x => (F x).1 i))+
      ∑ i : Fin 2,primalEnergy Q (Real.sqrt 3) (fun x => (F x).2 i) := by
  rw [oldSignedBlockPositiveNorm,Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  simp only [vectorPositiveHaarNorm,Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q _)]
  rfl

/-- The block-positive norm of a pure-second input retains exactly that
vector's positive norm; the first zero block contributes no energy. -/
theorem old_signed_pure_second_block_positive_sq (Q : TriadicCube 2) (f : Vec 2 → Vec 2) :
    oldSignedBlockPositiveNorm Q (fun x => (0,f x))^2=vectorPositiveHaarNorm Q f^2 := by
  rw [old_signed_block_positive_norm_sq,vectorPositiveHaarNorm,
    Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q f)]
  simp only [Pi.zero_apply,old_signed_primal_zero,Finset.sum_const_zero,zero_add]
  rfl

/-- The corresponding exact pure-first norm identity for the minus input. -/
theorem old_signed_pure_first_block_positive_sq (Q : TriadicCube 2) (f : Vec 2 → Vec 2) :
    oldSignedBlockPositiveNorm Q (fun x => (f x,0))^2=vectorPositiveHaarNorm Q f^2 := by
  rw [old_signed_block_positive_norm_sq,vectorPositiveHaarNorm,
    Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q f)]
  simp only [Pi.zero_apply,old_signed_primal_zero,Finset.sum_const_zero,add_zero]
  rfl

/-- Exact centered four-coordinate positive energy of an actual L2
source, including its full cell mean in the subtracted term. -/
theorem old_signed_block_positive_centering (Q : TriadicCube 2) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) :
    oldSignedBlockPositiveNorm Q (F-fun _ => oldSignedBlockMean Q F)^2=
      oldSignedBlockPositiveNorm Q F^2-
        blockVecDot (oldSignedBlockMean Q F) (oldSignedBlockMean Q F) := by
  rw [old_signed_block_positive_norm_sq,old_signed_block_positive_norm_sq]
  have hf i := memLp_normalized_of_memL2On ((memVectorL2_fst_of_memBlockL2 hF).eval i)
  have hg i := memLp_normalized_of_memL2On ((memVectorL2_snd_of_memBlockL2 hF).eval i)
  have h1 : (∑ i : Fin 2,primalEnergy Q (Real.sqrt 3)
      (fun x => (F x).1 i-(oldSignedBlockMean Q F).1 i))=
      (∑ i : Fin 2,primalEnergy Q (Real.sqrt 3) (fun x => (F x).1 i))-
        ∑ i : Fin 2,cubeAverage Q (fun x => (F x).1 i)^2 := by
    simp_rw [oldSignedBlockMean,old_signed_primal_sub_mean Q (Real.sqrt 3) _ (hf _)]
    rw [Finset.sum_sub_distrib]
  have h2 : (∑ i : Fin 2,primalEnergy Q (Real.sqrt 3)
      (fun x => (F x).2 i-(oldSignedBlockMean Q F).2 i))=
      (∑ i : Fin 2,primalEnergy Q (Real.sqrt 3) (fun x => (F x).2 i))-
        ∑ i : Fin 2,cubeAverage Q (fun x => (F x).2 i)^2 := by
    simp_rw [oldSignedBlockMean,old_signed_primal_sub_mean Q (Real.sqrt 3) _ (hg _)]
    rw [Finset.sum_sub_distrib]
  simp only [Pi.sub_apply,Prod.fst_sub,Prod.snd_sub]
  rw [h1,h2]
  simp only [oldSignedBlockMean,blockVecDot,vecDot,pow_two]
  ring

end
end ASDExplicitGamma.Native
