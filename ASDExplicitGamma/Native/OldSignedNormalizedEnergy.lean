module

public import ASDExplicitGamma.Native.OldSignedFlatDirichletEnergy
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Physical Hilbert L2 energy and the source normalized coordinate energy
agree exactly, including the cube-volume factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The normalized physical Hilbert-vector L2 energy equals the sum of
the actual normalized scalar coordinate energies. -/
theorem old_signed_vector_energy_normalization (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    (cubeVolume Q)⁻¹*‖toHilbertVectorL2OfVecField hF‖^2=
      ∑ k : Fin 2,energy Q (fun x => F x k) := by
  rw [←real_inner_self_eq_norm_sq,inner_toHilbertVectorL2OfVecField_eq_integral]
  simp_rw [energy_eq_integral_sq]
  rw [←integral_finsetSum _ (fun k _ =>
    (memLp_normalized_of_memL2On (hF.eval k)).integrable_sq),integral_normalized_eq_open]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  simp only [vecDot,pow_two]

/-- The exact Dirichlet orthogonal subtraction also holds in the source's
normalized spatial energies, for each actual white mode and load. -/
theorem old_signed_flat_minus_normalized_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    (∑ k : Fin 2,energy Q (fun x => oldSignedRotatedProjectedField b L (whiteBasis n) i x k)) =
      (∑ k : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,k) x))+
        ∑ k : Fin 2,energy Q (fun x => oldSignedFlatMinusRemainder Q b L n i x k) := by
  have h := congrArg (fun z : ℝ => (cubeVolume Q)⁻¹*z)
    (old_signed_flat_minus_energy_subtraction Q b L n i)
  rw [mul_add,old_signed_vector_energy_normalization,
    old_signed_vector_energy_normalization,old_signed_vector_energy_normalization] at h
  exact h

end
end ASDExplicitGamma.Native
