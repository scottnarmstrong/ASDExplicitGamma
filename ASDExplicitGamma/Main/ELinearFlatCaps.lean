module

public import ASDExplicitGamma.Main.ELinearPathwise
public import ASDExplicitGamma.Native.OldSignedFlatJointL2
public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy
public import ASDExplicitGamma.Native.OldSignedMinusRemainderEnergy

/-! Deterministic root caps of the flat L² profiles of the `L` group. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Triadic

/-- The complete minus flat L² profile of the root square is at most `b²`. -/
theorem main_flat_l2_minus_root_sq_le (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    oldSignedFlatL2Size Q Q b L false ^ 2 ≤ b ^ 2 := by
  rw [old_signed_flat_l2_size_sq]
  have hD := old_signed_flat_minus_complete_energy Q b L
  have hr0 : 0 ≤ ∑' n, oldSignedFlatMinusRemainderModeEnergy Q b L n :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun k _ => energy_nonneg Q _)))
  have hrt := hD.2.2.tsum_eq
  have hmode (n : whiteBasisIndex) :
      (∑ i : Fin 2, oldSignedBlockL2Energy Q (oldSignedFlatInput Q b L false n i)) =
        oldSignedFlatDirichletModeEnergy Q b L n := by
    simp [oldSignedBlockL2Energy, oldSignedFlatInput, oldSignedFlatMinusBlock,
      oldSignedFlatDirichletModeEnergy, energy_const]
  simp_rw [hmode]
  linarith

/-- The complete plus flat L² profile of the root square is `b² + B₀/2`. -/
theorem main_flat_l2_plus_root_sq_eq (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    oldSignedFlatL2Size Q Q b L true ^ 2 =
      b ^ 2 + oldSignedFlatBoundaryEnergy Q b L / 2 := by
  rw [old_signed_flat_l2_size_sq]
  have hmode (n : whiteBasisIndex) :
      (∑ i : Fin 2, oldSignedBlockL2Energy Q (oldSignedFlatInput Q b L true n i)) =
        oldSignedFlatPlusModeEnergy Q b L n := by
    simp [oldSignedBlockL2Energy, oldSignedFlatInput, oldSignedFlatPlusBlock,
      oldSignedFlatPlusModeEnergy, energy_const, energy_neg]
  simp_rw [hmode]
  have h1 := (old_signed_flat_plus_energy_trace Q b L).tsum_eq
  have h2 := old_signed_flat_boundary_energy_difference Q b L
  linarith

end ASDExplicitGamma.Main
