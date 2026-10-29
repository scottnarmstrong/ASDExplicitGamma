module

public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra
public import ASDExplicitGamma.Native.OldSignedShearFieldTransport

/-! Exact signed field expansions of the two actual OLD trial shapes.
The negative bottom cross and flat-tangent feedback retain their signs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian
noncomputable section

/-- Top trial expansion in the literal physical normalized field pairing. -/
theorem old_signed_top_field_trial_expansion (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {S A R : Vec 2 → BlockVec 2} (hS : MemBlockL2 (openCubeSet Q) S)
    (hA : MemBlockL2 (openCubeSet Q) A) (hR : MemBlockL2 (openCubeSet Q) R) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    E (A+R) (A+R)+2*E S (C (A+R))=
      E A A+E R R+2*E A R+2*E S (C A)+2*E S (C R) := by
  intro E C
  have hCA := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hA
  have hCR := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hR
  dsimp only [E]
  rw [old_signed_energy_pairing_add_left Q nu sigma hnu hsigma k hA hR (hA.add hR),
    old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k hA hA hR,
    old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k hR hA hR,
    old_signed_energy_pairing_symm Q nu sigma k R A,map_add,
    old_signed_energy_pairing_add_right Q nu sigma hnu hsigma k hS hCA hCR]
  ring

/-- Bottom trial expansion in the same physical field pairing, retaining
both the negative mixed cross and negative flat feedback. -/
theorem old_signed_bottom_field_trial_expansion (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex)
    {S R Z : Vec 2 → BlockVec 2} (hS : MemBlockL2 (openCubeSet Q) S)
    (hR : MemBlockL2 (openCubeSet Q) R) (hZ : MemBlockL2 (openCubeSet Q) Z) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    E (R-Z) (R-Z)+2*E S (C (R-Z))=
      E R R+E Z Z-2*E R Z+2*E S (C R)-2*E S (C Z) := by
  intro E C
  have hCR := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hR
  have hCZ := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n hZ
  dsimp only [E]
  rw [old_signed_energy_pairing_sub_left Q nu sigma hnu hsigma k hR hZ (hR.sub hZ),
    old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hR hR hZ,
    old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hZ hR hZ,
    old_signed_energy_pairing_symm Q nu sigma k Z R,map_sub,
    old_signed_energy_pairing_sub_right Q nu sigma hnu hsigma k hS hCR hCZ]
  ring

end
end ASDExplicitGamma.Native
