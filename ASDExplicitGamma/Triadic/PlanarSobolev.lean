module

public import ASDExplicitGamma.Triadic.VectorHaar
public import Homogenization.Sobolev.H1.Definitions

/-! Weak-derivative `W^{1,∞}` and `W^{2,∞}` interfaces on planar triadic cubes. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Triadic

/-- The Euclidean norm on planar vectors, written through the two coordinates. -/
noncomputable def planarEuclideanNorm (v : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Frobenius norm on planar matrices, written through their four entries. -/
noncomputable def planarFrobeniusNorm (A : Fin 2 → Fin 2 → ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- A vector field in `W^{1,∞}` on the open representative of a planar
triadic cube. Each coordinate is the public CoarseGraining `H1Function`
witness, and both the field and its weak derivative have finite `L∞` norm. -/
structure PlanarW1Infinity (Q : TriadicCube 2) where
  component : Fin 2 → H1Function (openCubeSet Q)
  component_memLp_top : ∀ i,
    MemLp (component i).toFun ⊤ (normalizedCubeMeasure Q)
  derivative_memLp_top : ∀ i j,
    MemLp (fun x => (component i).grad x j) ⊤ (normalizedCubeMeasure Q)

/-- The vector field represented by a planar `W^{1,∞}` witness. -/
noncomputable def planarW1Value {Q : TriadicCube 2} (b : PlanarW1Infinity Q) :
    Vec 2 → Fin 2 → ℝ :=
  fun x i => (b.component i).toFun x

/-- The weak derivative matrix represented by a planar `W^{1,∞}` witness;
the first index is the vector coordinate and the second is the derivative. -/
noncomputable def planarW1Derivative {Q : TriadicCube 2} (b : PlanarW1Infinity Q) :
    Vec 2 → Fin 2 → Fin 2 → ℝ :=
  fun x i j => (b.component i).grad x j

/-- The essential supremum of the Euclidean size of a planar `W^{1,∞}` field. -/
noncomputable def planarW1ValueLInf {Q : TriadicCube 2} (b : PlanarW1Infinity Q) : ℝ :=
  (eLpNorm (fun x => planarEuclideanNorm (planarW1Value b x)) ⊤
    (normalizedCubeMeasure Q)).toReal

/-- The essential supremum of the Frobenius size of the weak derivative of a
planar `W^{1,∞}` field. -/
noncomputable def planarW1DerivativeFrobeniusLInf {Q : TriadicCube 2}
    (b : PlanarW1Infinity Q) : ℝ :=
  (eLpNorm (fun x => planarFrobeniusNorm (planarW1Derivative b x)) ⊤
    (normalizedCubeMeasure Q)).toReal

/-- A scalar `W^{2,∞}` function on a planar triadic cube, represented by its
public `H1Function`, its two weak first derivatives as `W^{1,∞}` functions,
and the identification of those derivatives with its weak gradient. -/
structure PlanarW2Infinity (Q : TriadicCube 2) where
  value : H1Function (openCubeSet Q)
  value_memLp_top : MemLp value.toFun ⊤ (volume.restrict (openCubeSet Q))
  gradient : PlanarW1Infinity Q
  gradient_eq : ∀ i,
    (gradient.component i).toFun = fun x => value.grad x i

/-- The planar quarter-turn `J(v₁,v₂)=(-v₂,v₁)`. -/
def planarQuarterTurn (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -v 1 else v 0

/-- The vector field `J∇h` formed from the weak gradient of a planar
`W^{2,∞}` function. -/
noncomputable def planarJGradient {Q : TriadicCube 2} (h : PlanarW2Infinity Q) :
    Vec 2 → Fin 2 → ℝ :=
  fun x => planarQuarterTurn (fun i => h.value.grad x i)

/-- The essential supremum of `|∇h|` for a planar `W^{2,∞}` function. -/
noncomputable def planarGradientLInf {Q : TriadicCube 2} (h : PlanarW2Infinity Q) : ℝ :=
  planarW1ValueLInf h.gradient

/-- The essential supremum of the Frobenius norm of the weak Hessian of `h`. -/
noncomputable def planarHessianFrobeniusLInf {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) : ℝ :=
  planarW1DerivativeFrobeniusLInf h.gradient

end ASDExplicitGamma.Triadic
