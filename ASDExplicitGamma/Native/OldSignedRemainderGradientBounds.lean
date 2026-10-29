module

public import ASDExplicitGamma.Native.OldSignedRotatedGradientTrace

/-! AN (2.5) for the actual H1 harmonic remainder coordinates. Each
subtraction uses two complete physical families of exact sigma² trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Nonnegative actual coordinate derivative energies, independent of any
covariance series convergence. -/
theorem old_signed_coordinate_gradient_energy_nonneg (Q : TriadicCube 2)
    (F : Fin 2 × Fin 2 → H1Function (openCubeSet Q)) :
    0≤oldSignedCoordinateGradientEnergy Q F :=
  Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun a _ => energy_nonneg Q (fun x => (F a).grad x k)))

/-- Complete derivative-energy difference bound for genuine H1 coordinate
families. Summability is supplied by an actual summable nonnegative majorant. -/
theorem old_signed_coordinate_gradient_difference_tsum {I : Type*}
    (Q : TriadicCube 2) (F G : I → Fin 2 × Fin 2 → H1Function (openCubeSet Q))
    {A B : ℝ} (hF : HasSum (fun n => oldSignedCoordinateGradientEnergy Q (F n)) A)
    (hG : HasSum (fun n => oldSignedCoordinateGradientEnergy Q (G n)) B) :
    Summable (fun n => oldSignedCoordinateGradientEnergy Q (fun a => F n a-G n a)) ∧
      (∑' n,oldSignedCoordinateGradientEnergy Q (fun a => F n a-G n a))≤2*A+2*B := by
  have hmajor := (hF.mul_left 2).add (hG.mul_left 2)
  have hs := hmajor.summable.of_nonneg_of_le
    (fun n => old_signed_coordinate_gradient_energy_nonneg Q _)
    (fun n => old_signed_coordinate_gradient_difference_le Q (F n) (G n))
  refine ⟨hs,?_⟩
  exact (hs.tsum_le_tsum (fun n => old_signed_coordinate_gradient_difference_le Q (F n) (G n))
    hmajor.summable).trans_eq hmajor.tsum_eq

/-- Exact complete derivative trace for the actual minus Dirichlet field,
expressed in the same coordinate energy as the source remainders. -/
theorem old_signed_dirichlet_coordinate_gradient_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => oldSignedCoordinateGradientEnergy Q
      (mainFlatMinusCoordinate Q b L n)) (mainFlatSigmaSq b L) := by
  have hh := (mainFlatMinusGradientEnergy_tsum Q b L).1.hasSum
  rw [(mainFlatMinusGradientEnergy_tsum Q b L).2] at hh
  apply hh.congr_fun
  intro n
  exact old_signed_coordinate_gradient_energy_hilbert Q _

/-- Exact complete derivative trace for the actual rotated Dirichlet
correction removed from the plus field. -/
theorem old_signed_removed_coordinate_gradient_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => oldSignedCoordinateGradientEnergy Q
      (mainFlatPlusCorrectionCoordinate Q b L n)) (mainFlatSigmaSq b L) := by
  have hh := (mainFlatPlusCorrectionGradientEnergy_tsum Q b L).1.hasSum
  rw [(mainFlatPlusCorrectionGradientEnergy_tsum Q b L).2] at hh
  apply hh.congr_fun
  intro n
  exact old_signed_coordinate_gradient_energy_hilbert Q _

/-- The actual positive harmonic remainder has complete derivative energy
at most 4sigma², with its source H1 membership and summability supplied. -/
theorem old_signed_flat_plus_remainder_gradient_bound (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n : whiteBasisIndex => oldSignedCoordinateGradientEnergy Q
      (oldSignedFlatPlusRemainderCoordinateH1 Q b L n)) ∧
      (∑' n : whiteBasisIndex,oldSignedCoordinateGradientEnergy Q
        (oldSignedFlatPlusRemainderCoordinateH1 Q b L n))≤4*mainFlatSigmaSq b L := by
  have hh := old_signed_coordinate_gradient_difference_tsum Q
    (fun n => oldSignedComplementaryCoordinateH1 Q b L (whiteBasis n))
    (mainFlatPlusCorrectionCoordinate Q b L) (old_signed_complementary_gradient_trace Q b L)
    (old_signed_removed_coordinate_gradient_trace Q b L)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

/-- The actual negative harmonic remainder has complete derivative energy
at most 4sigma² on the same source square. -/
theorem old_signed_flat_minus_remainder_gradient_bound (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n : whiteBasisIndex => oldSignedCoordinateGradientEnergy Q
      (oldSignedFlatMinusRemainderCoordinateH1 Q b L n)) ∧
      (∑' n : whiteBasisIndex,oldSignedCoordinateGradientEnergy Q
        (oldSignedFlatMinusRemainderCoordinateH1 Q b L n))≤4*mainFlatSigmaSq b L := by
  have hh := old_signed_coordinate_gradient_difference_tsum Q
    (mainFlatMinusCoordinate Q b L) (fun n => oldSignedRotatedProjectedCoordinateH1 Q b L (whiteBasis n))
    (old_signed_dirichlet_coordinate_gradient_trace Q b L) (old_signed_rotated_projected_gradient_trace Q b L)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

end
end ASDExplicitGamma.Native
