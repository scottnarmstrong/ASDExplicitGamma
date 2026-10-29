module

public import ASDExplicitGamma.Native.OldSignedSharpFlatAffine
public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy

/-! Pure-second flat sources pair only with the reciprocal first defect. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic Inverse
noncomputable section

/-- The bottom-load reciprocal weak norm is paid by the directional proxy. -/
theorem old_signed_bottom_reciprocal_weak_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,e)
    vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux
      (responseFramePlanarCoefficientField nu sigma k) S x).2-e) ≤
      Real.sqrt (oldSignedDirectionalProxy Q (responseFramePlanarCoefficientField nu sigma k) e) := by
  intro S
  apply Real.sqrt_le_sqrt
  have hh := old_signed_bottom_directional_weak_bound Q nu sigma hnu hsigma k e
  exact (le_add_of_nonneg_left (vectorWeakHaarEnergy_nonneg Q (fun x => (S x).1))).trans hh

/-- The weak norm of a block field with zero first component is its second
vector weak norm. -/
theorem old_signed_pure_second_block_weak_norm (Q : TriadicCube 2) (g : Vec 2 → Vec 2) :
    oldSignedBlockWeakNorm Q (fun x => (0,g x))=vectorWeakHaarNorm Q g := by
  have hz : vectorWeakHaarEnergy Q (fun _ : Vec 2 => (0:Vec 2))=0 := by
    have hs := old_signed_vector_weak_projection_series Q (fun _ : Vec 2 => (0:Vec 2))
      (fun _ => memLp_const 0)
    rw [hs.2]
    have hp (j : ℕ) : cubeProjection Q j (fun _ : Vec 2 => (0:ℝ))=(fun _ => 0) := by
      simpa only [zero_mul,Pi.zero_apply] using projection_smul Q j (fun _ => (0:ℝ)) 0
    simp only [Pi.zero_apply,hp,energy,pairing,cubeAverage_const,mul_zero,
      Finset.sum_const_zero,tsum_zero]
  unfold oldSignedBlockWeakNorm
  simp only [vectorWeakHaarNorm,hz,Real.sqrt_zero,zero_pow (by decide : 2≠0),zero_add]
  exact Real.sqrt_sq (Real.sqrt_nonneg _)

/-- Pure-second fields need only the second flux component in Haar duality. -/
theorem old_signed_pure_second_pairing_bound (Q : TriadicCube 2)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hzero : ∀ x,(F x).1=0)
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).2 i)))) :
    |volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (G x))| ≤
      oldSignedBlockPositiveNorm Q F*vectorWeakHaarNorm Q (fun x => (G x).2) := by
  have hG' : MemBlockL2 (openCubeSet Q) (fun x => (0,(G x).2)) :=
    memBlockL2_blockField (memVectorL2_const 0) (memVectorL2_snd_of_memBlockL2 hG)
  have hh := old_signed_block_pairing_bound Q hF hG' hPfst hPsnd
  rw [old_signed_pure_second_block_weak_norm] at hh
  have he : (fun x => blockVecDot (F x) (0,(G x).2))=
      (fun x => blockVecDot (F x) (G x)) := by
    funext x
    simp [blockVecDot,hzero x,vecDot_zero_left]
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Native
