module

public import ASDExplicitGamma.Native.OldSignedComplementaryPairing
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthPositivity
public import ASDExplicitGamma.Scalar.FullResponseNorm

/-! Full compatible-mean coercivity in the actual physical coefficient.
The complementary canonical test controls both blocks together. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- Cauchy--Schwarz for the literal normalized physical energy. -/
theorem old_signed_energy_pairing_sq_le_product (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {F G : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F)
    (hG : MemBlockL2 (openCubeSet Q) G) :
    (oldSignedEnergyPairing Q nu sigma k F G)^2 ≤
      oldSignedEnergyPairing Q nu sigma k F F*oldSignedEnergyPairing Q nu sigma k G G := by
  exact blockPairingAverage_sq_le_product
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) (measurableSet_openCubeSet Q)
    ⟨fun x => (F x).1,fun x => (F x).2⟩ ⟨fun x => (G x).1,fun x => (G x).2⟩
    (old_signed_energy_pairing_integrable Q nu sigma hnu hsigma k hF hF)
    (old_signed_energy_pairing_integrable Q nu sigma hnu hsigma k hF hG)
    (old_signed_energy_pairing_integrable Q nu sigma hnu hsigma k hG hG)

/-- The complementary canonical test recovers the full mean of any
compatible field, with no Euler equation imposed on that field. -/
theorem old_signed_compatible_canonical_reflected_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → BlockVec 2} (hF : ScalarCompatible (openCubeSet Q) F) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k F (oldSignedDualReflection Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P))=
        blockVecDot (oldSignedBlockMean Q F) P.swap := by
  have hp := old_signed_canonical_error_variation Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k) P
  have hz := old_signed_compatible_reflected_variation_pairing Q nu sigma hnu hsigma k
    (F := F) (Y := fun x => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x-P) hF hp
  have he : (fun x => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x-P)=
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-(fun _ => P) := rfl
  rw [he] at hz
  rw [old_signed_dual_reflection_sub,old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hF.1
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)))
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k (memLp_const P))] at hz
  rw [sub_eq_zero] at hz
  rw [hz,old_signed_dual_reflection_pairing Q nu sigma hnu hsigma k]
  simpa only [blockVecDot_comm] using old_signed_constant_block_pairing_mean Q hF.1 P.swap

/-- Both components of a compatible field's mean are controlled together
by the full response norm and its energy, without a dimension loss. -/
theorem old_signed_compatible_full_mean_bound (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma) (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → BlockVec 2} (hF : ScalarCompatible (openCubeSet Q) F) :
    blockVecDot (oldSignedBlockMean Q F) (oldSignedBlockMean Q F) ≤
      fullResponseOperatorNorm Q (responseFramePlanarCoefficientField nu sigma k)*
        oldSignedEnergyPairing Q nu sigma k F F := by
  let p := oldSignedBlockMean Q F
  let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k p.swap
  have hS : MemBlockL2 (openCubeSet Q) S :=
    Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k p.swap)
  have hc := old_signed_energy_pairing_sq_le_product Q nu sigma hnu hsigma k hF.1
    (old_signed_dual_reflection_memL2 Q nu sigma hnu hsigma k hS)
  rw [old_signed_compatible_canonical_reflected_pairing Q nu sigma hnu hsigma k hF p.swap,
    old_signed_dual_reflection_isometry Q nu sigma hnu hsigma k] at hc
  change (blockVecDot p p)^2 ≤ oldSignedEnergyPairing Q nu sigma k F F*
    oldSignedEnergyPairing Q nu sigma k S S at hc
  have he := old_signed_canonical_energy Q nu sigma hnu hsigma k p.swap
  change oldSignedEnergyPairing Q nu sigma k S S=_ at he
  rw [he,←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q] at hc
  have hop := block_quadratic_le_operator_norm
    (coarseBlockMatrix (cubeSet Q) (responseFramePlanarCoefficientField nu sigma k)) p.swap
  have hnorm : blockVecDot p.swap p.swap=blockVecDot p p := by
    simp only [blockVecDot,Prod.swap]
    ring
  rw [hnorm] at hop
  have hE := old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k F
  have hh := hc.trans (mul_le_mul_of_nonneg_left hop hE)
  change (blockVecDot p p)^2 ≤ oldSignedEnergyPairing Q nu sigma k F F*
    (fullResponseOperatorNorm Q (responseFramePlanarCoefficientField nu sigma k)*blockVecDot p p) at hh
  have h0 := blockVecDot_nonneg p
  by_cases hp : blockVecDot p p=0
  · change blockVecDot p p ≤ _
    rw [hp]
    exact mul_nonneg (full_response_operator_norm_nonneg _ _) hE
  · have hp0 : 0<blockVecDot p p := lt_of_le_of_ne h0 (Ne.symm hp)
    have hmul : blockVecDot p p*blockVecDot p p ≤
        (fullResponseOperatorNorm Q (responseFramePlanarCoefficientField nu sigma k)*
          oldSignedEnergyPairing Q nu sigma k F F)*blockVecDot p p := by
      nlinarith only [hh]
    exact (mul_le_mul_iff_left₀ hp0).mp hmul

end
end ASDExplicitGamma.Native
