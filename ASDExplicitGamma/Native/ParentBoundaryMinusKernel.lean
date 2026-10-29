module

public import ASDExplicitGamma.Native.ParentBoundarySourceClock
public import ASDExplicitGamma.Native.ParentBoundaryRowH1
public import ASDExplicitGamma.Native.OldSignedCoordinateKernel

/-! Complete physical flat-minus kernels, with their sharp actual energy
and derivative traces. These are full fields, not harmonic remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Complete value trace of the actual four flat-minus coordinates. -/
theorem parent_boundary_minus_coordinate_value_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    HasSum (fun n : whiteBasisIndex => ∑ a : Fin 2 × Fin 2,energy Q (mainFlatMinusCoordinate Q b L n a))
      (parentBoundaryDirichletEnergy Q b L) := by
  have hs := (old_signed_flat_minus_complete_energy Q b L).1.hasSum
  apply hs.congr_fun
  intro n
  rw [Fintype.sum_prod_type]
  rfl

/-- Complete derivative trace of those SAME physical coordinates is sigma². -/
theorem parent_boundary_minus_coordinate_gradient_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    HasSum (fun n : whiteBasisIndex => ∑ k : Fin 2,∑ a : Fin 2 × Fin 2,
      energy Q (fun x => (mainFlatMinusCoordinate Q b L n a).grad x k)) (mainFlatSigmaSq b L) :=
  old_signed_dirichlet_coordinate_gradient_trace Q b L

/-- The actual complete white-Hilbert kernel of one full minus coordinate. -/
def parentBoundaryMinusKernel (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) : HilbertH1Function (openCubeSet Q) WhiteNoise :=
  oldSignedCoordinateKernel Q whiteBasis (mainFlatMinusCoordinate Q b L)
    (parent_boundary_minus_coordinate_value_trace Q b L).summable
    (parent_boundary_minus_coordinate_gradient_trace Q b L).summable a

/-- Exact complete value energy is the physical Y, with no boundary proxy. -/
theorem parent_boundary_minus_kernel_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (∑ a : Fin 2 × Fin 2,hilbertEnergy Q (parentBoundaryMinusKernel Q b L a).toFun) =
      parentBoundaryDirichletEnergy Q b L := by
  unfold parentBoundaryMinusKernel
  rw [old_signed_coordinate_kernel_energy]
  exact (parent_boundary_minus_coordinate_value_trace Q b L).tsum_eq

/-- Exact complete gradient energy is the physical sigma². -/
theorem parent_boundary_minus_kernel_gradient_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (∑ a : Fin 2 × Fin 2,hilbertGradientEnergy Q (parentBoundaryMinusKernel Q b L a).grad) =
      mainFlatSigmaSq b L := by
  unfold parentBoundaryMinusKernel
  rw [old_signed_coordinate_kernel_gradient_energy]
  exact (parent_boundary_minus_coordinate_gradient_trace Q b L).tsum_eq

/-- Each coefficient of this complete Hilbert kernel is the original
actual flat-minus coordinate on the physical parent square. -/
theorem parent_boundary_minus_kernel_coefficient (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) (n : whiteBasisIndex) :
    (fun x => inner ℝ (whiteBasis n) ((parentBoundaryMinusKernel Q b L a).toFun x))
      =ᵐ[normalizedCubeMeasure Q] mainFlatMinusCoordinate Q b L n a := by
  have hh := old_signed_h1_kernel_coefficient Q whiteBasis
    (fun j => mainFlatMinusCoordinate Q b L j a)
    (old_signed_coordinate_value_summable Q _
      (parent_boundary_minus_coordinate_value_trace Q b L).summable a)
    (old_signed_coordinate_derivative_summable Q _
      (parent_boundary_minus_coordinate_gradient_trace Q b L).summable a) n
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hh

/-- The scalar full covariance coordinate is a genuine H1 row product. -/
def parentBoundaryMinusCovarianceH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  parentBoundaryRowH1 whiteBasis Q (q3Section b L h3Zero)
    (old_signed_white_section_contDiff b L) (parentBoundaryMinusKernel Q b L a)

end
end ASDExplicitGamma.Native
