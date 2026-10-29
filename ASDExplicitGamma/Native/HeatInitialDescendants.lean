module

public import ASDExplicitGamma.Native.HeatInitialFreshMoment
public import ASDExplicitGamma.Cold.NativeCellIndex
public import ASDExplicitGamma.Native.HeatInitialCrossRow
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Scalar.LawShiftCarrier
public import Algsuperdiff.Section4.Provider.Annular.DescendantLattice
public import ASDExplicitGamma.Triadic.DiagMesh

/-! Geometry and fresh-band moments on the actual depth-nine descendants. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Section4.Provider.Annular
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators

-- The generated q3 finite-sum types make the constructor-name linter recurse
-- past its budget; this check is orthogonal to the explicit proofs below.
set_option linter.constructorNameAsVariable false

/-- The lower-left corner of a parent is the origin for its canonical q3 grid. -/
noncomputable def nativeHeatQ3ParentOrigin (Q : TriadicCube 2) : Vec 2 :=
  fun a => Triadic.cubeCorner Q a

-- The concrete old/fresh cross row follows after its finite child family and
-- fresh vector are identified with this parent's depth-nine mesh.

end ASDExplicitGamma.Native
