module

public import ASDExplicitGamma.Native.OldSignedPureSecondSourceEnergy
public import ASDExplicitGamma.Native.OldSignedWeakPositiveComparison

/-! Sharp inverse-history reciprocal oscillation for pure-second sources. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- A pure-second source pays B, rather than sqrt(B M), for its actual
reciprocal residual norm. -/
theorem old_signed_pure_second_inverse_reciprocal_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (G : Vec 2 → BlockVec 2)
    (hG : MemBlockL2 (openCubeSet Q) G) (hzero : ∀ x,(G x).1=0)
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (G x).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (G x).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG)
    vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a Z x).2) ≤
      oldSignedInverseHistory Q a*oldSignedBlockPositiveNorm Q G := by
  intro a Z
  have he := old_signed_residual_reciprocal_weak_energy Q nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hG)
  have hs := old_signed_pure_second_source_energy Q nu sigma hnu hsigma k G hG hzero hPfst hPsnd
  have hB : 0≤oldSignedInverseHistory Q a :=
    lemmaVInverseHistory_nonneg Q a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hr := Real.sqrt_le_sqrt (he.trans (mul_le_mul_of_nonneg_left hs hB))
  change vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a Z x).2) ≤
    Real.sqrt (oldSignedInverseHistory Q a*(oldSignedInverseHistory Q a*
      oldSignedBlockPositiveNorm Q G^2)) at hr
  have hO : 0≤oldSignedBlockPositiveNorm Q G := Real.sqrt_nonneg _
  rw [show oldSignedInverseHistory Q a*(oldSignedInverseHistory Q a*
      oldSignedBlockPositiveNorm Q G^2)=(oldSignedInverseHistory Q a*oldSignedBlockPositiveNorm Q G)^2 by ring,
    Real.sqrt_sq (mul_nonneg hB hO)] at hr
  exact hr

/-- Subtracting the input costs one additional positive-Haar norm. -/
theorem old_signed_pure_second_inverse_reciprocal_defect (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (G : Vec 2 → BlockVec 2)
    (hG : MemBlockL2 (openCubeSet Q) G) (hzero : ∀ x,(G x).1=0)
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (G x).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (G x).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG)
    vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a Z x).2-(G x).2) ≤
      (oldSignedInverseHistory Q a+1)*oldSignedBlockPositiveNorm Q G := by
  intro a Z
  let J := scalarCoefficientFlux a Z
  have hJ := scalar_coefficient_flux_memL2 Q a
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) (Lp.memLp Z)
  have hJc (i : Fin 2) := memLp_normalized_of_memL2On
    (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hJ) i)
  have hGc (i : Fin 2) := memLp_normalized_of_memL2On
    (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hG) i)
  have hh := old_signed_vector_weak_triangle Q hJc (fun i => (hGc i).neg)
  change vectorWeakHaarNorm Q (fun x => (J x).2+(-(G x).2)) ≤
    vectorWeakHaarNorm Q (fun x => (J x).2)+vectorWeakHaarNorm Q (fun x => -(G x).2) at hh
  rw [old_signed_vector_weak_neg] at hh
  have hg := (old_signed_vector_weak_le_positive Q hGc hPsnd).trans
    (old_signed_block_snd_positive_le Q G)
  have hj := old_signed_pure_second_inverse_reciprocal_norm Q nu sigma hnu hsigma k G hG hzero hPfst hPsnd
  simpa only [sub_eq_add_neg,add_mul,one_mul] using hh.trans (add_le_add hj hg)

end
end ASDExplicitGamma.Native
