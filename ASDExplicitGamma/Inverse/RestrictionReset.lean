module

public import ASDExplicitGamma.Inverse.ResetChronology
public import ASDExplicitGamma.Inverse.HistoryConversion
public import ASDExplicitGamma.Model.LocalIndependenceSupports
public import ASDExplicitGamma.Inverse.StoppedPlanarHeight
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring

/-! The order-dependent entrance, protected old labels, and stopped height. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The source order band `ceil(log₃(max(1,p/64)))`. -/
noncomputable def orderBand (p : ℝ) : ℕ :=
  Nat.ceil (Real.log (max 1 (p / 64)) / Real.log 3)

/-- The entrance at the source order band. -/
def heightEntrance (k : ℕ) : ℕ := 377 + 12 * k

/-- The maximal protected old label read by the construction. -/
def protectedOldLabel (l : ℤ) (k : ℕ) : ℤ := l - 342 - 12 * k

/-- The Whitney layer profile, before adding its selected height. -/
def layerProfile (i : ℕ) : ℕ := i + (i + 2) / 3

/-- Fine depth of layer `i` at stopped height `h`. -/
def layerDepth (h i : ℕ) : ℕ := layerProfile i + h + 3

/-- The old coefficient label read on this layer, with buffer forty. -/
def layerOldCutoff (l : ℤ) (h i : ℕ) : ℤ :=
  l - (layerDepth h i : ℤ) + 40

theorem layer_old_cutoff_le_protected (l : ℤ) (k h i : ℕ)
    (hh : heightEntrance k ≤ h) (hi : 1 ≤ i) :
    layerOldCutoff l h i ≤ protectedOldLabel l k := by
  have hprofile : 2 ≤ layerProfile i := by
    unfold layerProfile
    omega
  unfold layerOldCutoff layerDepth layerProfile heightEntrance
    protectedOldLabel at *
  push_cast
  omega

end ASDExplicitGamma.Inverse
