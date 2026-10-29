module

public import ASDExplicitGamma.Main.Q3ColumnProduct
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates

/-! The full actual source-column Hilbert--Schmidt sum, without a rank hypothesis. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian
open scoped BigOperators

/-- The literal positive-Haar energy of one source derivative column. -/
noncomputable def mainQ3DerivativeColumnEnergy {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : H10Function (openCubeSet Q)) (j : ι) : ℝ :=
  ∑ i : Fin 2, primalEnergy Q (Real.sqrt 3)
    (fun x => u.toH1Function.toFun x*
      (fderiv ℝ (q3Convolution b L h3Zero (e j)) x) (basisVec i))

end ASDExplicitGamma.Main
