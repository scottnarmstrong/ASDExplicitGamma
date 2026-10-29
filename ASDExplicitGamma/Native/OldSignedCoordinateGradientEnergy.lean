module

public import ASDExplicitGamma.Native.OldSignedRemainderCoordinateH1

/-! Finite coordinate gradient-energy comparisons, with exact bridges to
the existing Hilbert H1 flat fields. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- The actual Frobenius derivative energy of a four-coordinate H1 field. -/
def oldSignedCoordinateGradientEnergy (Q : TriadicCube 2)
    (F : Fin 2 × Fin 2 → H1Function (openCubeSet Q)) : ℝ :=
  ∑ k : Fin 2,∑ a : Fin 2 × Fin 2,energy Q (fun x => (F a).grad x k)

/-- The finite coordinate energy is the existing Hilbert H1 derivative
energy, with no component or normalization loss. -/
theorem old_signed_coordinate_gradient_energy_hilbert (Q : TriadicCube 2)
    (F : Fin 2 × Fin 2 → H1Function (openCubeSet Q)) :
    oldSignedCoordinateGradientEnergy Q F=hilbertGradientEnergy Q (mainHilbertH1OfCoordinates Q F).grad := by
  unfold oldSignedCoordinateGradientEnergy hilbertGradientEnergy
  apply Finset.sum_congr rfl
  intro k _
  rw [main_hilbertEnergy_euclidean Q ((mainHilbertH1OfCoordinates Q F).gradMemL2_normalized Q k)]
  rfl

/-- Scalar normalized energy satisfies the exact factor-two difference
bound, proved from pointwise squares and actual L2 integrability. -/
theorem old_signed_energy_sub_le (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x-g x)≤2*energy Q f+2*energy Q g := by
  rw [energy_eq_integral_sq,energy_eq_integral_sq,energy_eq_integral_sq]
  have hi : Integrable (fun x => 2*f x^2+2*g x^2) (normalizedCubeMeasure Q) := by
    exact (hf.integrable_sq.const_mul 2).add (hg.integrable_sq.const_mul 2)
  calc
    _ ≤ ∫ x,2*f x^2+2*g x^2 ∂normalizedCubeMeasure Q :=
      integral_mono_ae (hf.sub hg).integrable_sq hi (Filter.Eventually.of_forall
        (fun x => by
          change (f x-g x)^2≤2*f x^2+2*g x^2
          nlinarith only [sq_nonneg (f x+g x)]))
    _ = _ := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hg.integrable_sq.const_mul 2),
        integral_const_mul,integral_const_mul]

/-- A difference of actual coordinate H1 fields has the factor-two
Frobenius derivative bound. -/
theorem old_signed_coordinate_gradient_difference_le (Q : TriadicCube 2)
    (F G : Fin 2 × Fin 2 → H1Function (openCubeSet Q)) :
    oldSignedCoordinateGradientEnergy Q (fun a => F a-G a)≤
      2*oldSignedCoordinateGradientEnergy Q F+2*oldSignedCoordinateGradientEnergy Q G := by
  have hp (k : Fin 2) (a : Fin 2 × Fin 2) :
      energy Q (fun x => (F a-G a).grad x k)≤
        2*energy Q (fun x => (F a).grad x k)+2*energy Q (fun x => (G a).grad x k) := by
    simp only [H1Function.sub_grad,Pi.sub_apply]
    exact old_signed_energy_sub_le Q ((F a).grad_memL2_normalizedCubeMeasure k)
      ((G a).grad_memL2_normalizedCubeMeasure k)
  unfold oldSignedCoordinateGradientEnergy
  calc
    _ ≤ ∑ k : Fin 2,∑ a : Fin 2 × Fin 2,
        (2*energy Q (fun x => (F a).grad x k)+2*energy Q (fun x => (G a).grad x k)) :=
      Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun a _ => hp k a))
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.mul_sum]

end
end ASDExplicitGamma.Native
