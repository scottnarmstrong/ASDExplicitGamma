module

public import ASDExplicitGamma.Cold.NativeFrameTrace
public import ASDExplicitGamma.Cold.SquareMatchedOptimizers
public import Homogenization.Book.Ch04.Theorems.CanonicalSolutions.Measurability

/-! # Genuine canonical response optimizers for the fixed native coefficient -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- The public canonical response solution on an actual cell, retyped to the exact scalar carrier. -/
def coldCanonicalOptimizer (a : RegCoeffField 2) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube 2) (p q : Vec 2) : AHarmonicFunction a.toFun (openCubeSet Q) :=
  (Ch02.canonicalMaximizer (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
    ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)) p q).toSolution

/-- The public selected solution is an actual source response maximizer. -/
theorem coldCanonicalOptimizer_max (a : RegCoeffField 2) (ha : Ch04.AELocallyUniformlyEllipticField a)
    (Q : TriadicCube 2) (p q : Vec 2) :
    IsResponseMaximizer (openCubeSet Q) p q a.toFun (coldCanonicalOptimizer a ha Q p q) := by
  intro w
  exact (Ch02.canonicalMaximizer (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
    ((Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn Q)) p q).isMaximizer w

/-- Native canonical optimizer at every sample and actual parent/cell cube. -/
def coldNativeOptimizer (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (p q : Vec 2)
    (ω : Cutoff.CutoffSample 2) : AHarmonicFunction (coldNativeCoefficient M m ω).toFun (openCubeSet Q) :=
  coldCanonicalOptimizer (coldNativeCoefficient M m ω) (coldNativeCoefficient_locallyElliptic M m ω) Q p q

end ASDExplicitGamma.Cold
