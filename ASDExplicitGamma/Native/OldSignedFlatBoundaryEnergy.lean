module

public import ASDExplicitGamma.Native.OldSignedFlatBoundaryMode
public import ASDExplicitGamma.Native.OldSignedRawEnergyTrace

/-! The actual source Bflat is twice either complete harmonic remainder
energy. All complete physical series are proved convergent. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Per actual white mode, raw energy equals all-gradient flat energy plus
the energy removed by the zero-normal solenoidal projection. -/
theorem old_signed_flat_raw_mode_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x =>
      (q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) k))=
      oldSignedFlatPlusModeEnergy Q b L n+oldSignedFlatDirichletModeEnergy Q b L n := by
  have hi (i : Fin 2) : (∑ k : Fin 2,energy Q (fun x =>
      (q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) k))=
      (∑ k : Fin 2,energy Q (fun x => mainFlatPlusCoordinate Q b L n (i,k) x))+
        ∑ k : Fin 2,energy Q (fun x => oldSignedFlatRemovedField Q b L n i x k) := by
    have hh := old_signed_normalized_energy_add_potential_solenoidal Q
      (old_signed_flat_plus_memL2 Q b L n i) (old_signed_flat_removed_memL2 Q b L n i)
      (old_signed_flat_plus_potential Q b L n i) (old_signed_flat_removed_zero_normal Q b L n i)
    have he (k : Fin 2) : (fun x => ((fun k => mainFlatPlusCoordinate Q b L n (i,k) x)+
        oldSignedFlatRemovedField Q b L n i x) k)=(fun x =>
        (q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) k) := by
      funext x
      simp only [oldSignedFlatRemovedField,Pi.add_apply,Pi.sub_apply]
      ring
    simp_rw [he] at hh
    exact hh
  simp_rw [hi]
  rw [Finset.sum_add_distrib,old_signed_flat_removed_energy_sum]
  rfl

/-- The all-gradient flat energy has its exact complete white trace. -/
theorem old_signed_flat_plus_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (oldSignedFlatPlusModeEnergy Q b L)
      (2*b^2-∑' n,oldSignedFlatDirichletModeEnergy Q b L n) := by
  have hh := (old_signed_rotated_raw_energy_trace Q b L).sub
    (old_signed_flat_minus_complete_energy Q b L).1.hasSum
  apply hh.congr_fun
  intro n
  rw [old_signed_flat_raw_mode_energy]
  ring

/-- Actual complete harmonic boundary energy in the OLD physical square. -/
def oldSignedFlatBoundaryEnergy (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  ∑' n,oldSignedFlatBoundaryModeEnergy Q b L n

/-- The actual Bflat series converges, and its exact trace is 2v-2y². -/
theorem old_signed_flat_boundary_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (oldSignedFlatBoundaryModeEnergy Q b L)
      (2*(b^2-∑' n,oldSignedFlatDirichletModeEnergy Q b L n)) := by
  have hh := (old_signed_flat_plus_energy_trace Q b L).sub
    (old_signed_flat_minus_complete_energy Q b L).1.hasSum
  have hs : HasSum (oldSignedFlatBoundaryModeEnergy Q b L)
      ((2*b^2-∑' n,oldSignedFlatDirichletModeEnergy Q b L n)-
        ∑' n,oldSignedFlatDirichletModeEnergy Q b L n) := by
    apply hh.congr_fun
    intro n
    rw [old_signed_flat_boundary_mode_energy]
    ring
  convert hs using 1
  ring

/-- AN (1.3): the full actual flat energy difference equals Bflat. -/
theorem old_signed_flat_boundary_energy_difference (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    (∑' n,oldSignedFlatPlusModeEnergy Q b L n)-
      (∑' n,oldSignedFlatDirichletModeEnergy Q b L n)=oldSignedFlatBoundaryEnergy Q b L := by
  rw [(old_signed_flat_plus_energy_trace Q b L).tsum_eq,
    oldSignedFlatBoundaryEnergy,(old_signed_flat_boundary_energy_trace Q b L).tsum_eq]
  ring

/-- AN (2.4): both actual harmonic remainder energies equal Bflat/2,
with convergence of both mode series already established. -/
theorem old_signed_flat_remainder_energies_half_boundary (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    (∑' n,oldSignedFlatPlusRemainderModeEnergy Q b L n)=oldSignedFlatBoundaryEnergy Q b L/2 ∧
      (∑' n,oldSignedFlatMinusRemainderModeEnergy Q b L n)=oldSignedFlatBoundaryEnergy Q b L/2 := by
  rw [(old_signed_flat_plus_complete_energy Q b L).tsum_eq,
    (old_signed_flat_minus_complete_energy Q b L).2.2.tsum_eq,
    oldSignedFlatBoundaryEnergy,(old_signed_flat_boundary_energy_trace Q b L).tsum_eq]
  constructor <;> ring

end
end ASDExplicitGamma.Native
