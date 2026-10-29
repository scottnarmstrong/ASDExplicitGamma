module

public import ASDExplicitGamma.Native.OldSignedH1KernelEnergy
public import ASDExplicitGamma.Native.OldSignedCoordinateGradientEnergy

/-! Coordinatewise white-Hilbert reconstruction with exact aggregate
energies. No coordinate estimate is assumed separately from the physical
complete value and gradient energies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- A finite coordinate is dominated by its complete nonnegative energy. -/
theorem old_signed_coordinate_value_summable {I A : Type*} [Fintype A]
    (Q : TriadicCube 2) (u : I → A → H1Function (openCubeSet Q))
    (hu : Summable (fun n => ∑ a,energy Q (u n a))) (a : A) :
    Summable (fun n => energy Q (u n a)) :=
  hu.of_nonneg_of_le (fun _n => energy_nonneg Q _) (fun n =>
    Finset.single_le_sum (fun a _ => energy_nonneg Q (u n a)) (Finset.mem_univ a))

/-- The same domination supplies each actual derivative coordinate. -/
theorem old_signed_coordinate_derivative_summable {I A : Type*} [Fintype A]
    (Q : TriadicCube 2) (u : I → A → H1Function (openCubeSet Q))
    (hdu : Summable (fun n => ∑ k : Fin 2,∑ a,energy Q (fun x => (u n a).grad x k)))
    (a : A) (k : Fin 2) :
    Summable (fun n => energy Q (fun x => (u n a).grad x k)) := by
  apply hdu.of_nonneg_of_le (fun n => energy_nonneg Q _)
  intro n
  exact (Finset.single_le_sum (fun a _ => energy_nonneg Q (fun x => (u n a).grad x k))
    (Finset.mem_univ a)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun a _ => energy_nonneg Q
      (fun x => (u n a).grad x k))) (Finset.mem_univ k))

/-- The actual coordinate kernel produced from complete value and gradient
summability, retaining every white direction. -/
def oldSignedCoordinateKernel {E I A : Type*} [Fintype A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → A → H1Function (openCubeSet Q))
    (hu : Summable (fun n => ∑ a,energy Q (u n a)))
    (hdu : Summable (fun n => ∑ k : Fin 2,∑ a,energy Q (fun x => (u n a).grad x k)))
    (a : A) : HilbertH1Function (openCubeSet Q) E :=
  oldSignedNormalizedH1Kernel Q e (fun n => u n a)
    (old_signed_coordinate_value_summable Q u hu a)
    (old_signed_coordinate_derivative_summable Q u hdu a)

/-- Aggregate kernel value energy is precisely the complete mode energy. -/
theorem old_signed_coordinate_kernel_energy {E I A : Type*} [Fintype A] [Countable I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → A → H1Function (openCubeSet Q))
    (hu : Summable (fun n => ∑ a,energy Q (u n a)))
    (hdu : Summable (fun n => ∑ k : Fin 2,∑ a,energy Q (fun x => (u n a).grad x k))) :
    (∑ a,hilbertEnergy Q (oldSignedCoordinateKernel Q e u hu hdu a).toFun)=
      ∑' n,∑ a,energy Q (u n a) := by
  simp only [oldSignedCoordinateKernel,old_signed_h1_kernel_energy]
  exact (hasSum_sum (s := Finset.univ)
    (fun a _ => (old_signed_coordinate_value_summable Q u hu a).hasSum)).tsum_eq.symm

/-- Aggregate kernel gradient energy is precisely the complete derivative
energy, with both coordinate and spatial sums in their literal source order. -/
theorem old_signed_coordinate_kernel_gradient_energy {E I A : Type*} [Fintype A] [Countable I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube 2) (e : HilbertBasis I ℝ E)
    (u : I → A → H1Function (openCubeSet Q))
    (hu : Summable (fun n => ∑ a,energy Q (u n a)))
    (hdu : Summable (fun n => ∑ k : Fin 2,∑ a,energy Q (fun x => (u n a).grad x k))) :
    (∑ a,hilbertGradientEnergy Q (oldSignedCoordinateKernel Q e u hu hdu a).grad)=
      ∑' n,∑ k : Fin 2,∑ a,energy Q (fun x => (u n a).grad x k) := by
  simp only [hilbertGradientEnergy,oldSignedCoordinateKernel,old_signed_h1_kernel_gradient_energy]
  rw [Finset.sum_comm]
  exact (hasSum_sum (s := Finset.univ) (fun k _ =>
    hasSum_sum (s := Finset.univ) (fun a _ =>
      (old_signed_coordinate_derivative_summable Q u hdu a k).hasSum))).tsum_eq.symm


end
end ASDExplicitGamma.Native
