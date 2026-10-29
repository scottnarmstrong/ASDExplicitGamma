module

public import ASDExplicitGamma.Cold.NativeCanonicalOptimizer
public import ASDExplicitGamma.Cold.ColdPlateauFamily

/-! # An actual canonical optimizer family at one native coefficient and true frame -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- Every adjoint normalized sample has the same source local ellipticity bounds. -/
theorem coldNativeAdjoint_locallyElliptic (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    Ch04.AELocallyUniformlyEllipticField (adjointReg (coldNativeCoefficient M m ω)) := by
  intro Q
  obtain ⟨Λ,hEll⟩ := coldNativeCoefficient_elliptic M m Q ω
  have hO := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  obtain ⟨x,hx⟩ := cold_openCubeSet_nonempty Q
  exact ⟨coldNativeLower M m,Λ,coldNativeLower_pos M m,(hO.2 x hx).2.1,
    IsAEEllipticFieldOn.of_isEllipticFieldOn (isEllipticFieldOn_adjointCoeffField hO)⟩

/-- The four actual canonical matched optimizers on any actual source cell. -/
def coldNativeMatchedOptimizers (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : SquareMatchedOptimizers Q (coldNativeCoefficient M m ω).toFun where
  primal := fun i => coldNativeOptimizer M m Q (Pi.single i 1) (Pi.single i 1) ω
  adjoint := fun i => coldCanonicalOptimizer (adjointReg (coldNativeCoefficient M m ω))
    (coldNativeAdjoint_locallyElliptic M m ω) Q (Pi.single i 1) (Pi.single i 1)
  primal_max := fun i => coldCanonicalOptimizer_max (coldNativeCoefficient M m ω)
    (coldNativeCoefficient_locallyElliptic M m ω) Q (Pi.single i 1) (Pi.single i 1)
  adjoint_max := fun i => coldCanonicalOptimizer_max (adjointReg (coldNativeCoefficient M m ω))
    (coldNativeAdjoint_locallyElliptic M m ω) Q (Pi.single i 1) (Pi.single i 1)

/-- Actual source family for P1--P6, with the same coefficient and canonical parent at every depth. -/
def coldNativePlateauFamily (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    ColdPlateauFamily Q (Cutoff.CutoffSample 2) where
  coefficient := fun ω => (coldNativeCoefficient M m ω).toFun
  lower := fun _ => coldNativeLower M m
  upper := fun ω => Classical.choose (coldNativeCoefficient_elliptic M m Q ω)
  elliptic := fun ω => (Classical.choose_spec (coldNativeCoefficient_elliptic M m Q ω)).mono
    (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  parent := coldNativeMatchedOptimizers M m Q
  cells := fun _ ω R => coldNativeMatchedOptimizers M m R.val ω

/-- Parent traces of the actual normalized family are literally the true-frame native trace. -/
theorem coldNativePlateauFamily_parentTrace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (r : ℕ) (ω : Cutoff.CutoffSample 2) :
    ((coldNativePlateauFamily M m Q).atDepth r).parentTrace ω = coldNativeCellTrace M m Q ω :=
  (coldNativeCellTrace_eq_normalized M m Q ω).symm

/-- Every own-cell trace is the genuine translated trace on that same cell. -/
theorem coldNativePlateauFamily_cellTrace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (r : ℕ) (R : SquareCells Q r) (ω : Cutoff.CutoffSample 2) :
    ((coldNativePlateauFamily M m Q).atDepth r).cellTrace R ω = coldNativeCellTrace M m R.val ω :=
  (coldNativeCellTrace_eq_normalized M m R.val ω).symm

end ASDExplicitGamma.Cold
