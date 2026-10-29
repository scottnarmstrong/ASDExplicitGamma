module

public import ASDExplicitGamma.Native.OldSignedNormalizedEnergy

/-! Pythagoras for actual normalized vector field energies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Genuine L2 orthogonal fields have additive normalized physical energy. -/
theorem old_signed_normalized_energy_add_of_orthogonal (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2} (hF : MemVectorL2 (openCubeSet Q) F)
    (hG : MemVectorL2 (openCubeSet Q) G)
    (ho : (∫ x in openCubeSet Q,vecDot (F x) (G x) ∂volume)=0) :
    (∑ k : Fin 2,energy Q (fun x => (F x+G x) k))=
      (∑ k : Fin 2,energy Q (fun x => F x k))+
        ∑ k : Fin 2,energy Q (fun x => G x k) := by
  have hh := norm_add_sq_real (toHilbertVectorL2OfVecField hF) (toHilbertVectorL2OfVecField hG)
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hF hG,ho,mul_zero,add_zero,
    ←toHilbertVectorL2OfVecField_add hF hG] at hh
  have he := congrArg (fun z : ℝ => (cubeVolume Q)⁻¹*z) hh
  rw [mul_add,old_signed_vector_energy_normalization,old_signed_vector_energy_normalization,
    old_signed_vector_energy_normalization] at he
  exact he

/-- The normalized energy of a genuine gradient is orthogonal to every
actual zero-normal solenoidal field, as required for OLD's plus remainder. -/
theorem old_signed_normalized_energy_add_potential_solenoidal (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2} (hF : MemVectorL2 (openCubeSet Q) F)
    (hG : MemVectorL2 (openCubeSet Q) G) (hp : IsPotentialOn (openCubeSet Q) F)
    (hs : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) G) :
    (∑ k : Fin 2,energy Q (fun x => (F x+G x) k))=
      (∑ k : Fin 2,energy Q (fun x => F x k))+
        ∑ k : Fin 2,energy Q (fun x => G x k) := by
  apply old_signed_normalized_energy_add_of_orthogonal Q hF hG
  obtain ⟨u,hu⟩ := hp
  simpa only [hu,vecDot_comm] using hs u

end
end ASDExplicitGamma.Native
