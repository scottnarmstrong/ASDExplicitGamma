/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.SeriesHeat
public import Algsuperdiff.Assumptions.ShellField.Basic
public import Mathlib.Topology.CompactOpen
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Measurability of the shell-field restriction

The zero-shell law uses the Borel measurable space of the compact-open topology on
`ShellField`. Restricting its scalar stream to a subset is continuous for the
compact-open topologies, hence measurable for the Borel structures.
-/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

open Algsuperdiff.Frozen.Assumptions Homogenization Topology

/-- The scalar `(1,0)` matrix entry, viewed as a continuous linear-coordinate map. -/
def planarShellMatrixEntry : C(Homogenization.Mat 2, ℝ) where
  toFun A := A 1 0
  continuous_toFun := (continuous_apply 0).comp (continuous_apply 1)

/-- The scalar stream stored in a planar frozen shell field. -/
def planarShellScalarStream (j : ShellField 2) : C(Homogenization.Vec 2, ℝ) :=
  planarShellMatrixEntry.comp j.1.1

/-- Restriction of the planar scalar stream to an arbitrary subset. -/
def shellFieldScalarRestriction (K : Set (Homogenization.Vec 2))
    (j : ShellField 2) : C(K, ℝ) :=
  (planarShellScalarStream j).restrict K

/-- The compact-open restriction map on the frozen shell carrier is continuous. -/
theorem continuous_shellFieldScalarRestriction (K : Set (Homogenization.Vec 2)) :
    Continuous (shellFieldScalarRestriction K) := by
  exact (ContinuousMap.continuous_restrict K).comp
    ((ContinuousMap.continuous_postcomp planarShellMatrixEntry).comp
      continuous_subtype_val.fst)

/-- The shell-field restriction is measurable for Superdiffusion's Borel shell law and the
Borel structure on `C(K, ℝ)`. -/
theorem measurable_shellFieldScalarRestriction (K : Set (Homogenization.Vec 2)) :
    Measurable (shellFieldScalarRestriction K) :=
  (continuous_shellFieldScalarRestriction K).measurable

end ASDExplicitGamma.Gaussian
