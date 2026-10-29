module

public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates

/-! Complete scalar-coordinate value and gradient energy series of the
actual OLD flat fields, extracted from their full physical traces. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- A coordinate of a genuine finite nonnegative energy trace is summable. -/
theorem old_signed_finite_series_component {I A : Type*} [Fintype A]
    (f : I → A → ℝ) (hf : ∀ n a,0≤f n a)
    (hs : Summable (fun n => ∑ a : A,f n a)) (a : A) : Summable (fun n => f n a) := by
  classical
  exact hs.of_nonneg_of_le (fun n => hf n a) (fun n =>
    Finset.single_le_sum (fun b _ => hf n b) (Finset.mem_univ a))

/-- Actual H1 coordinate gradients retain every component of the complete
Hilbert gradient trace. -/
theorem old_signed_h1_coordinate_gradient_series {I A : Type*} [Fintype A]
    (Q : TriadicCube 2) (f : I → A → H1Function (openCubeSet Q))
    (hs : Summable (fun n => hilbertGradientEnergy Q (mainHilbertH1OfCoordinates Q (f n)).grad))
    (a : A) (j : Fin 2) : Summable (fun n => energy Q (fun x => (f n a).grad x j)) := by
  have he (n : I) : hilbertGradientEnergy Q (mainHilbertH1OfCoordinates Q (f n)).grad=
      ∑ j : Fin 2,∑ a : A,energy Q (fun x => (f n a).grad x j) := by
    unfold hilbertGradientEnergy
    apply Finset.sum_congr rfl
    intro k _
    rw [main_hilbertEnergy_euclidean Q ((mainHilbertH1OfCoordinates Q (f n)).gradMemL2_normalized Q k)]
    rfl
  have ht := hs.congr he
  have hj := old_signed_finite_series_component _
    (fun n k => Finset.sum_nonneg (fun c _ => energy_nonneg Q _)) ht j
  exact old_signed_finite_series_component _ (fun n c => energy_nonneg Q _) hj a

/-- Complete plus-flat coordinate value energy. -/
theorem old_signed_flat_plus_value_series (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) :
    Summable (fun n : whiteBasisIndex => energy Q (mainFlatPlusCoordinate Q b L n a).toFun) := by
  have hs : Summable (fun n : whiteBasisIndex => ∑ c : Fin 2 × Fin 2,
      energy Q (mainFlatPlusCoordinate Q b L n c).toFun) := by
    have h := (old_signed_flat_plus_energy_trace Q b L).summable
    change Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ k : Fin 2,
      energy Q (fun x => mainFlatPlusCoordinate Q b L n (i,k) x)) at h
    simpa only [Fintype.sum_prod_type] using h
  exact old_signed_finite_series_component _ (fun n c => energy_nonneg Q _) hs a

/-- Complete minus-flat coordinate value energy. -/
theorem old_signed_flat_minus_value_series (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) :
    Summable (fun n : whiteBasisIndex => energy Q (mainFlatMinusCoordinate Q b L n a).toFun) := by
  have hs : Summable (fun n : whiteBasisIndex => ∑ c : Fin 2 × Fin 2,
      energy Q (mainFlatMinusCoordinate Q b L n c).toFun) := by
    have h := (old_signed_flat_minus_complete_energy Q b L).1
    change Summable (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ k : Fin 2,
      energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,k) x)) at h
    simpa only [Fintype.sum_prod_type] using h
  exact old_signed_finite_series_component _ (fun n c => energy_nonneg Q _) hs a

/-- Complete plus-flat coordinate derivative energy. -/
theorem old_signed_flat_plus_gradient_series (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) (j : Fin 2) :
    Summable (fun n : whiteBasisIndex => energy Q (fun x => (mainFlatPlusCoordinate Q b L n a).grad x j)) :=
  old_signed_h1_coordinate_gradient_series Q (fun n => mainFlatPlusCoordinate Q b L n)
    (mainFlatPlusGradientEnergy_tsum Q b L).1 a j

/-- Complete minus-flat coordinate derivative energy. -/
theorem old_signed_flat_minus_gradient_series (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) (j : Fin 2) :
    Summable (fun n : whiteBasisIndex => energy Q (fun x => (mainFlatMinusCoordinate Q b L n a).grad x j)) :=
  old_signed_h1_coordinate_gradient_series Q (fun n => mainFlatMinusCoordinate Q b L n)
    (mainFlatMinusGradientEnergy_tsum Q b L).1 a j

end
end ASDExplicitGamma.Native
