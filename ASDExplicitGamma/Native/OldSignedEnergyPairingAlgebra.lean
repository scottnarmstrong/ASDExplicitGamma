module

public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! Literal field bilinearity of the actual fixed-frame OLD energy,
with integrability proved before splitting the normalized spatial integral. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
noncomputable section

/-- Genuine integrability of a physical doubled coefficient pairing. -/
theorem old_signed_energy_pairing_integrable (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    IntegrableOn (fun x => blockVecDot (F x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (G x)))
      (openCubeSet Q) := by
  have hflux := scalar_coefficient_flux_memL2 Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) hG
  have hh := (integrableOn_vecDot_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF)
    (memVectorL2_fst_of_memBlockL2 hflux)).add
    (integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF)
      (memVectorL2_snd_of_memBlockL2 hflux))
  exact hh.congr_fun_ae (Filter.Eventually.of_forall (fun _ => rfl))

/-- The actual doubled coefficient is symmetric, before spatial integration. -/
theorem old_signed_energy_pairing_symm (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k F G=oldSignedEnergyPairing Q nu sigma k G F := by
  unfold oldSignedEnergyPairing
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  exact blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm _ _ _

/-- Left additivity of the literal normalized energy pairing. -/
theorem old_signed_energy_pairing_add_left (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G H : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hH : MemBlockL2 (openCubeSet Q) H) :
    oldSignedEnergyPairing Q nu sigma k (F+G) H=
      oldSignedEnergyPairing Q nu sigma k F H+oldSignedEnergyPairing Q nu sigma k G H := by
  unfold oldSignedEnergyPairing
  change volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x+G x) _)=_
  simp_rw [blockVecDot_add_left]
  exact volumeAverage_add (old_signed_energy_pairing_integrable Q nu sigma hnu hsigma k hF hH)
    (old_signed_energy_pairing_integrable Q nu sigma hnu hsigma k hG hH)

/-- Right additivity in the same actual coefficient pairing. -/
theorem old_signed_energy_pairing_add_right (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G H : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hH : MemBlockL2 (openCubeSet Q) H) :
    oldSignedEnergyPairing Q nu sigma k F (G+H)=
      oldSignedEnergyPairing Q nu sigma k F G+oldSignedEnergyPairing Q nu sigma k F H := by
  rw [old_signed_energy_pairing_symm Q nu sigma k F (G+H),
    old_signed_energy_pairing_add_left Q nu sigma hnu hsigma k hG hH hF,
    old_signed_energy_pairing_symm Q nu sigma k G F,old_signed_energy_pairing_symm Q nu sigma k H F]

/-- Exact sign change in the left field; the normalized integral retains it. -/
theorem old_signed_energy_pairing_neg_left (Q : TriadicCube 2) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k (-F) G= -oldSignedEnergyPairing Q nu sigma k F G := by
  unfold oldSignedEnergyPairing
  have he : (fun x => blockVecDot ((-F) x)
      (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (G x)))=
      fun x => -blockVecDot (F x)
        (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x) (G x)) := by
    funext x
    simp [blockVecDot,vecDot,Finset.sum_neg_distrib]
    ring
  rw [he]
  simp only [volumeAverage,integral_neg]
  ring

/-- Left subtraction of genuine physical fields. -/
theorem old_signed_energy_pairing_sub_left (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G H : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hH : MemBlockL2 (openCubeSet Q) H) :
    oldSignedEnergyPairing Q nu sigma k (F-G) H=
      oldSignedEnergyPairing Q nu sigma k F H-oldSignedEnergyPairing Q nu sigma k G H := by
  rw [sub_eq_add_neg F G,old_signed_energy_pairing_add_left Q nu sigma hnu hsigma k hF hG.neg hH,
    old_signed_energy_pairing_neg_left]
  rfl

/-- Right subtraction in the same actual physical pairing. -/
theorem old_signed_energy_pairing_sub_right (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G H : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hH : MemBlockL2 (openCubeSet Q) H) :
    oldSignedEnergyPairing Q nu sigma k F (G-H)=
      oldSignedEnergyPairing Q nu sigma k F G-oldSignedEnergyPairing Q nu sigma k F H := by
  rw [old_signed_energy_pairing_symm Q nu sigma k F (G-H),
    old_signed_energy_pairing_sub_left Q nu sigma hnu hsigma k hG hH hF,
    old_signed_energy_pairing_symm Q nu sigma k G F,old_signed_energy_pairing_symm Q nu sigma k H F]

end
end ASDExplicitGamma.Native
