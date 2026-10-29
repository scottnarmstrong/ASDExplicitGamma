module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialRepresentative
public import ASDExplicitGamma.Inverse.LaterBandW2

/-! Exact pointwise split of the physical compatible field into its scalar
fresh skew forcing and the literal stationary potential correction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Frozen.Assumptions Gaussian Inverse
noncomputable section

/-- Raw physical forcing uses the very same scalar band as the sensitivity
Sobolev witness, with the fixed OLD-frame weight c. -/
theorem upper_cell_raw_forcing_scalar_band
    (n terminal : ℤ) (c : ℝ) (e : Vec 2) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) (i : Fin 2) :
    (valuePathForcing (c • e) (shellSumValuePath n terminal (x +ᵥ ω).val)).ofLp i =
      laterScalarBand n terminal (fun _ => c) ω x * matVecMul Response.responsePlanarJ e i := by
  change matVecMul (shellSumValuePath n terminal (x +ᵥ ω).val 0) (c • e) i = _
  have ht : shellSumValuePath n terminal (x +ᵥ ω).val = x +ᵥ shellSumValuePath n terminal ω.val :=
    shellSumValuePath_translateSequence n terminal x ω.val
  rw [ht,ShellField.vadd_apply,zero_add,
    shellSumValuePath_apply,matVecMul_finiteShellIncrement_apply]
  have hp (k : ℤ) : shellRowForcing (c • e) x i k ω.val =
      (c*shellScalarValue (ω.val k) x) * matVecMul Response.responsePlanarJ e i := by
    change matVecMul (ω.val k x) (c • e) i = _
    rw [lambda8Q3ShellMatVec_eq_scalarJ]
    change (ω.val k x 1 0) * matVecMul Response.responsePlanarJ (c • e) i =
      (c*(ω.val k x 1 0)) * matVecMul Response.responsePlanarJ e i
    simp only [matVecMul,Fin.sum_univ_two,Pi.smul_apply,smul_eq_mul]
    ring
  simp_rw [hp]
  exact (Finset.sum_mul _ _ _).symm

/-- Physical corrected flux, coordinate by coordinate, with the actual
scalar perturbation and the actual potential representative. -/
theorem upper_cell_physical_flux_coordinate_split
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) (i : Fin 2) :
    (realize (cutoffBandFlux M n terminal c e) ω x).ofLp i =
      laterScalarBand n terminal (fun _ => c) ω x * matVecMul Response.responsePlanarJ e i +
        (realize (upperCellPotentialRepr M n terminal c e) ω x).ofLp i := by
  rw [upper_cell_physical_flux_split]
  change (valuePathForcing (c • e) (shellSumValuePath n terminal (x +ᵥ ω).val)).ofLp i + _ = _
  rw [upper_cell_raw_forcing_scalar_band]
  rfl

/-- Literal physical potential mean, taken over the whole cube on the same sample. -/
def upperCellPhysicalPotentialMean (M : ABKModel 2) (n terminal : ℤ) (c : ℝ)
    (e : Vec 2) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) : Vec 2 :=
  fun i => cubeAverage Q (fun x => (realize (upperCellPotentialRepr M n terminal c e) ω x).ofLp i)

end
end ASDExplicitGamma.Scalar
