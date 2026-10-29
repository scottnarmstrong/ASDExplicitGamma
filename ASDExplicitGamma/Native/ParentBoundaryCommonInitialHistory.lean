module

public import ASDExplicitGamma.Native.ParentBoundaryBandMaxTraceMoment
public import ASDExplicitGamma.Inverse.HistoryTrace
public import ASDExplicitGamma.Native.OldSignedInitialHistory

/-! Exact native strong-history input to every actual simultaneous parent band. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Zero insertion is exactly the original physical completed coefficient. -/
theorem parent_boundary_common_band_coefficient_zero
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt 0) ω =
      (Cutoff.coefficientCutoff M.nu n ω).toFun := by
  funext x
  simp [attenuatedCoefficient]

end
end ASDExplicitGamma.Native
