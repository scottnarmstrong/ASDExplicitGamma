module

public import ASDExplicitGamma.Native.OldSignedFlatRemovedEnergy
public import ASDExplicitGamma.Native.OldSignedOrthogonalEnergy

/-! Actual orthogonal subtraction and complete energy for the positive
harmonic remainder, with the same Dirichlet bill as the negative remainder. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- Actual local L2 membership of the removed zero-normal field. -/
theorem old_signed_flat_removed_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (oldSignedFlatRemovedField Q b L n i) :=
  (old_signed_rotated_raw_load_memL2 Q b L (whiteBasis n) i).sub (old_signed_flat_plus_memL2 Q b L n i)

/-- The removed field has the actual zero-normal trace. -/
theorem old_signed_flat_removed_zero_normal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (oldSignedFlatRemovedField Q b L n i) := by
  rw [old_signed_flat_removed_field]
  exact planarJ_gradient_isSolenoidalZeroNormalTrace (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n)

/-- For each actual mode and load, the complementary whole-plane energy
splits orthogonally into positive remainder and zero-normal removed energy. -/
theorem old_signed_flat_plus_normalized_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    (∑ k : Fin 2,energy Q (fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) i x k))=
      (∑ k : Fin 2,energy Q (fun x => oldSignedFlatPlusRemainder Q b L n i x k))+
        ∑ k : Fin 2,energy Q (fun x => oldSignedFlatRemovedField Q b L n i x k) := by
  have hh := old_signed_normalized_energy_add_potential_solenoidal Q
    (old_signed_flat_remainders_memL2 Q b L n i).1 (old_signed_flat_removed_memL2 Q b L n i)
    (old_signed_flat_plus_remainder_potential Q b L n i) (old_signed_flat_removed_zero_normal Q b L n i)
  have he (k : Fin 2) : (fun x => (oldSignedFlatPlusRemainder Q b L n i x+
      oldSignedFlatRemovedField Q b L n i x) k)=
      fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) i x k := by
    funext x
    simp only [oldSignedFlatPlusRemainder,oldSignedFlatRemovedField,oldSignedRotatedComplementaryField,
      Pi.add_apply,Pi.sub_apply]
    ring
  simp_rw [he] at hh
  exact hh

/-- Actual normalized energy of both positive harmonic remainders. -/
def oldSignedFlatPlusRemainderModeEnergy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => oldSignedFlatPlusRemainder Q b L n i x k)

/-- The complete positive remainder has the exact same energy bill as the
complete negative remainder. No finite-rank family is called stationary. -/
theorem old_signed_flat_plus_complete_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (oldSignedFlatPlusRemainderModeEnergy Q b L)
      (b^2-∑' n,oldSignedFlatDirichletModeEnergy Q b L n) := by
  have hp := old_signed_rotated_complementary_energy_trace Q b L
  have hy := (old_signed_flat_minus_complete_energy Q b L).1
  have hh := hp.sub hy.hasSum
  apply hh.congr_fun
  intro n
  have he : (∑ i : Fin 2,∑ k : Fin 2,energy Q
      (fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) i x k)) =
      oldSignedFlatPlusRemainderModeEnergy Q b L n+oldSignedFlatDirichletModeEnergy Q b L n := by
    simp_rw [old_signed_flat_plus_normalized_energy]
    rw [Finset.sum_add_distrib,old_signed_flat_removed_energy_sum]
    rfl
  rw [he]
  ring

end
end ASDExplicitGamma.Native
