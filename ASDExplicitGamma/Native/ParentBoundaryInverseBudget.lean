module

public import ASDExplicitGamma.Native.SmallerGamma
public import ASDExplicitGamma.Numerics.Native.SetupParent001
public import ASDExplicitGamma.Numerics.Native.SetupParent002
public import ASDExplicitGamma.Numerics.Native.SetupParent003
public import ASDExplicitGamma.Numerics.Native.SetupParent004
public import ASDExplicitGamma.Numerics.Native.SetupParent005
public import ASDExplicitGamma.Numerics.Native.SetupParent006
public import ASDExplicitGamma.Numerics.Native.SetupParent007
public import ASDExplicitGamma.Numerics.Native.SetupParent008
public import ASDExplicitGamma.Numerics.Native.SetupParent009
public import ASDExplicitGamma.Numerics.Native.SetupParent010
public import ASDExplicitGamma.Numerics.Native.SetupParent011
public import ASDExplicitGamma.Numerics.Native.SetupParent012
public import ASDExplicitGamma.Numerics.Native.SetupParent013
public import ASDExplicitGamma.Numerics.Native.SetupParent014
public import ASDExplicitGamma.Numerics.Native.SetupParent015
public import ASDExplicitGamma.Numerics.Native.SetupParent016
public import ASDExplicitGamma.Native.ParentBoundaryInverseBandReturn
public import ASDExplicitGamma.Native.ParentBoundaryInverseClock

/-! Rational inverse-cost budgets for all sixteen direct parent panels.
The budgets will be connected to the actual signed inverse integral. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
open ASDExplicitGamma.Numerics.Native
noncomputable section

/-- The finite rational physical shell-variance majorant at gammaZero. -/
def parentBoundaryVarianceBudget (height : ℕ) : ℚ :=
  (9/2)*(17/50000)*(1-(11/10)*(2*(height:ℚ)*(17/50000)))⁻¹

/-- A finite geometric Dirichlet clock; each shell keeps its own decay. -/
def parentBoundaryInverseYBudget (height : ℕ) : ℚ :=
  (26/15)*parentBoundaryVarianceBudget height*
    ∑ i∈Finset.range height,(1/9:ℚ)^(i+1)

/-- The global-bank inverse drift clock, with a rational unit covariance cap. -/
def parentBoundaryInverseKBudget (height : ℕ) : ℚ :=
  (232/125)*(14103/10000)^2*(height:ℚ)*parentBoundaryVarianceBudget height

/-- The complete correlated reserve, normalized by the global bank baseline. -/
def parentBoundaryInverseRhoBudget : ℚ :=
  4*(1/10^24)+6*(1/10^24)^2/(14103/10000)+2*(1/10^24)^3/(14103/10000)^2

/-- A simple linear signed inverse-cost allocation. -/
def parentBoundaryInverseCostBudget (height : ℕ) : ℚ :=
  parentBoundaryInverseYBudget height*(2+parentBoundaryInverseRhoBudget)*
    parentBoundaryInverseKBudget height/2

/-- The actual real inverse-cost output already enclosed by the source setup. -/
def parentBoundarySetupInverseCost (j : Fin 16) : ℝ :=
  [nativeSetupParent001InvcostR,nativeSetupParent002InvcostR,nativeSetupParent003InvcostR,nativeSetupParent004InvcostR,nativeSetupParent005InvcostR,nativeSetupParent006InvcostR,nativeSetupParent007InvcostR,nativeSetupParent008InvcostR,nativeSetupParent009InvcostR,nativeSetupParent010InvcostR,nativeSetupParent011InvcostR,nativeSetupParent012InvcostR,nativeSetupParent013InvcostR,nativeSetupParent014InvcostR,nativeSetupParent015InvcostR,nativeSetupParent016InvcostR].getD j.val 0

/-- The lower endpoint of the source setup's inverse-cost interval. -/
def parentBoundarySetupInverseLower (j : Fin 16) : ℚ :=
  [nativeSetupParent001InvcostI.lo,nativeSetupParent002InvcostI.lo,nativeSetupParent003InvcostI.lo,nativeSetupParent004InvcostI.lo,nativeSetupParent005InvcostI.lo,nativeSetupParent006InvcostI.lo,nativeSetupParent007InvcostI.lo,nativeSetupParent008InvcostI.lo,nativeSetupParent009InvcostI.lo,nativeSetupParent010InvcostI.lo,nativeSetupParent011InvcostI.lo,nativeSetupParent012InvcostI.lo,nativeSetupParent013InvcostI.lo,nativeSetupParent014InvcostI.lo,nativeSetupParent015InvcostI.lo,nativeSetupParent016InvcostI.lo].getD j.val 0

/-- All sixteen actual source inverse-cost intervals dominate the simple
rational allocation. This checks exact rationals in the kernel. -/
theorem parent_boundary_inverse_budget_numeric (j : Fin 16) :
    parentBoundaryInverseCostBudget (j.val+1)≤parentBoundarySetupInverseLower j := by
  fin_cases j <;> decide +kernel

/-- The lower interval endpoint bounds the SAME real setup output. -/
theorem parent_boundary_inverse_setup_lower (j : Fin 16) :
    (parentBoundarySetupInverseLower j:ℝ)≤parentBoundarySetupInverseCost j := by
  fin_cases j <;> simp only [parentBoundarySetupInverseLower,parentBoundarySetupInverseCost,
    List.getD_cons_zero,List.getD_cons_succ]
  · have hh : Numerics.QInterval.Contains nativeSetupParent001InvcostI nativeSetupParent001InvcostR :=
      nativeSetupParent001_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent002InvcostI nativeSetupParent002InvcostR :=
      nativeSetupParent002_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent003InvcostI nativeSetupParent003InvcostR :=
      nativeSetupParent003_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent004InvcostI nativeSetupParent004InvcostR :=
      nativeSetupParent004_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent005InvcostI nativeSetupParent005InvcostR :=
      nativeSetupParent005_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent006InvcostI nativeSetupParent006InvcostR :=
      nativeSetupParent006_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent007InvcostI nativeSetupParent007InvcostR :=
      nativeSetupParent007_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent008InvcostI nativeSetupParent008InvcostR :=
      nativeSetupParent008_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent009InvcostI nativeSetupParent009InvcostR :=
      nativeSetupParent009_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent010InvcostI nativeSetupParent010InvcostR :=
      nativeSetupParent010_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent011InvcostI nativeSetupParent011InvcostR :=
      nativeSetupParent011_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent012InvcostI nativeSetupParent012InvcostR :=
      nativeSetupParent012_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent013InvcostI nativeSetupParent013InvcostR :=
      nativeSetupParent013_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent014InvcostI nativeSetupParent014InvcostR :=
      nativeSetupParent014_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent015InvcostI nativeSetupParent015InvcostR :=
      nativeSetupParent015_sound 0
    exact hh.1
  · have hh : Numerics.QInterval.Contains nativeSetupParent016InvcostI nativeSetupParent016InvcostR :=
      nativeSetupParent016_sound 0
    exact hh.1

end
end ASDExplicitGamma.Native
