module

public import ASDExplicitGamma.Native.OldSignedCoordinateKernel
public import ASDExplicitGamma.Native.OldSignedRemainderGradientBounds
public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy

/-! The two actual physical harmonic remainders as complete white-Hilbert
H1 kernels, with exact half-boundary value energies and sharp derivative
energy bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- Select one of the two actual harmonic remainder coordinate families. -/
def oldSignedRemainderCoordinate (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) : whiteBasisIndex → Fin 2 × Fin 2 → H1Function (openCubeSet Q) :=
  if plus then oldSignedFlatPlusRemainderCoordinateH1 Q b L else oldSignedFlatMinusRemainderCoordinateH1 Q b L

/-- The exact complete value energy of either actual remainder family. -/
theorem old_signed_remainder_coordinate_value_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    HasSum (fun n => ∑ a,energy Q (oldSignedRemainderCoordinate Q b L plus n a))
      (oldSignedFlatBoundaryEnergy Q b L/2) := by
  have hp := (old_signed_flat_plus_complete_energy Q b L).summable.hasSum
  have hm := (old_signed_flat_minus_complete_energy Q b L).2.1.hasSum
  rw [(old_signed_flat_remainder_energies_half_boundary Q b L).1] at hp
  rw [(old_signed_flat_remainder_energies_half_boundary Q b L).2] at hm
  cases plus
  · apply hm.congr_fun
    intro n
    simp only [oldSignedRemainderCoordinate,Bool.false_eq_true,↓reduceIte,
      Fintype.sum_prod_type,oldSignedFlatMinusRemainderModeEnergy]
    congr 1
    funext i
    congr 1
    funext k
    congr 1
    funext x
    exact old_signed_flat_minus_remainder_coordinate_toFun Q b L n i k x
  · apply hp.congr_fun
    intro n
    simp only [oldSignedRemainderCoordinate,↓reduceIte,
      Fintype.sum_prod_type,oldSignedFlatPlusRemainderModeEnergy]
    congr 1
    funext i
    congr 1
    funext k
    congr 1
    funext x
    exact old_signed_flat_plus_remainder_coordinate_toFun Q b L n i k x

/-- Actual complete derivative summability and the source 4sigma² bound. -/
theorem old_signed_remainder_coordinate_gradient_bound (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    Summable (fun n => ∑ k : Fin 2,∑ a,energy Q
      (fun x => (oldSignedRemainderCoordinate Q b L plus n a).grad x k)) ∧
      (∑' n,∑ k : Fin 2,∑ a,energy Q
        (fun x => (oldSignedRemainderCoordinate Q b L plus n a).grad x k))≤4*mainFlatSigmaSq b L := by
  cases plus
  · exact old_signed_flat_minus_remainder_gradient_bound Q b L
  · exact old_signed_flat_plus_remainder_gradient_bound Q b L

/-- The complete physical white-Hilbert harmonic remainder kernel. -/
def oldSignedRemainderKernel (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) (a : Fin 2 × Fin 2) : HilbertH1Function (openCubeSet Q) WhiteNoise :=
  oldSignedCoordinateKernel Q whiteBasis (oldSignedRemainderCoordinate Q b L plus)
    (old_signed_remainder_coordinate_value_trace Q b L plus).summable
    (old_signed_remainder_coordinate_gradient_bound Q b L plus).1 a

/-- Exact AN (2.4) for the actual reconstructed kernels. -/
theorem old_signed_remainder_kernel_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    (∑ a,hilbertEnergy Q (oldSignedRemainderKernel Q b L plus a).toFun)=
      oldSignedFlatBoundaryEnergy Q b L/2 := by
  simp only [oldSignedRemainderKernel]
  rw [old_signed_coordinate_kernel_energy]
  exact (old_signed_remainder_coordinate_value_trace Q b L plus).tsum_eq

/-- Exact AN (2.5) for the same actual reconstructed kernels. -/
theorem old_signed_remainder_kernel_gradient_bound (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    (∑ a,hilbertGradientEnergy Q (oldSignedRemainderKernel Q b L plus a).grad)≤4*mainFlatSigmaSq b L := by
  simp only [oldSignedRemainderKernel]
  rw [old_signed_coordinate_kernel_gradient_energy]
  exact (old_signed_remainder_coordinate_gradient_bound Q b L plus).2

end
end ASDExplicitGamma.Native
