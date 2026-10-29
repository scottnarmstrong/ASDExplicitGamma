module

public import ASDExplicitGamma.Native.OldSignedFlatCoordinateSeries
public import ASDExplicitGamma.Native.OldSignedH1PositiveSeries
public import ASDExplicitGamma.Native.OldSignedFlatBlockFields
public import ASDExplicitGamma.Native.OldSignedDerivativeRow

/-! Actual complete cellwise positive source series for both OLD flat
inputs, with the plus sign convention retained and arbitrary means allowed. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- The actual negative plus-flat source has a complete summable cellwise
positive-norm square series on every chosen finite partition. -/
theorem old_signed_flat_plus_source_cell_energy_summable (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => vectorPositiveHaarNorm U
      (fun x => (oldSignedFlatPlusBlock Q b L n i x).2)^2) := by
  have h := old_signed_h1_vector_positive_descendant_series Q depth
    (fun n k => mainFlatPlusCoordinate Q b L n (i,k))
    (fun k => old_signed_flat_plus_value_series Q b L (i,k))
    (fun k j => old_signed_flat_plus_gradient_series Q b L (i,k) j) U hU
  change Summable (fun n : whiteBasisIndex => vectorPositiveHaarNorm U
    (fun x k => -mainFlatPlusCoordinate Q b L n (i,k) x)^2)
  simp_rw [old_signed_vector_positive_neg]
  exact h

/-- The actual minus-flat source has the complete positive-norm square
series required by the cell projection bounds. -/
theorem old_signed_flat_minus_source_cell_energy_summable (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun n : whiteBasisIndex => vectorPositiveHaarNorm U
      (fun x => (oldSignedFlatMinusBlock Q b L n i x).1)^2) :=
  old_signed_h1_vector_positive_descendant_series Q depth
    (fun n k => mainFlatMinusCoordinate Q b L n (i,k))
    (fun k => old_signed_flat_minus_value_series Q b L (i,k))
    (fun k j => old_signed_flat_minus_gradient_series Q b L (i,k) j) U hU

/-- Every actual plus-flat coordinate, with any affine mean removed,
has the genuine positive Haar increments on the chosen cell. -/
theorem old_signed_flat_plus_cell_centered_positive (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (c : Vec 2) (k : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => (oldSignedFlatPlusBlock Q b L n i x).2 k-c k))) := by
  let u := fun a => (mainFlatPlusCoordinate Q b L n (i,a)).restrict
    (isOpen_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have h := old_signed_centered_h1_vector_positive_summable U u c (-1) k
  simpa only [u,H1Function.restrict,oldSignedFlatPlusBlock,neg_one_mul] using h

/-- Every actual minus-flat coordinate retains positive-Haar convergence
under removal of its actual cell mean. -/
theorem old_signed_flat_minus_cell_centered_positive (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (c : Vec 2) (k : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => (oldSignedFlatMinusBlock Q b L n i x).1 k-c k))) := by
  let u := fun a => (mainFlatMinusCoordinate Q b L n (i,a)).restrict
    (isOpen_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have h := old_signed_centered_h1_vector_positive_summable U u c 1 k
  simpa only [u,H1Function.restrict,oldSignedFlatMinusBlock,one_mul] using h

end
end ASDExplicitGamma.Native
