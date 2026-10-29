module

public import ASDExplicitGamma.Main.EOscillationMinimizer
public import ASDExplicitGamma.Main.Q3MultiplierScale
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Main.Q3RowCaps
public import ASDExplicitGamma.Main.Q3ColumnProduct
public import ASDExplicitGamma.Main.ColumnProductCaps
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Native.OldSignedCellProjection

/-! Actual cell-indexed affine minimizers for the OLD oscillation row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff
open scoped BigOperators

noncomputable section

/-- Restricting the partial OLD insertion coefficient from a parent to one
descendant gives exactly the coefficient defined on that cell. -/
theorem mainInsertionSkewCoefficient_cell_eq (Q R : TriadicCube 2)
    (hR : openCubeSet R ⊆ openCubeSet Q) (m : ℤ) (t : ℝ)
    (ω : CutoffSample 2) :
    oldSignedCellCoefficient Q R hR
        (mainInsertionSkewCoefficient m t Q ω) =
      mainInsertionSkewCoefficient m t R ω := by
  apply BoundedContinuousFunction.ext
  intro x
  simp only [oldSignedCellCoefficient,
    BoundedContinuousFunction.compContinuous_apply,
    mainInsertionSkewCoefficient]
  rfl

end

end ASDExplicitGamma.Main

end
