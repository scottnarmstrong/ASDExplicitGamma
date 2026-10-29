module

public import ASDExplicitGamma.Scalar.DirichletSquareHessian
public import ASDExplicitGamma.Triadic.HilbertPoincareNumerics
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1

/-! A zero-trace Dirichlet gradient is a genuine Hilbert-valued H1 field
whenever its scalar potential has a weak L2 Hessian. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Triadic
open scoped BigOperators

/-- The vector gradient of an H2 scalar function, with its weak Hessian as
the Hilbert-valued weak gradient. -/
noncomputable def lambda8HessianGradientH1 (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    HilbertH1Function (openCubeSet Q) (HilbertVec 2) := by
  let v := u.toH1Function
  refine {
    toFun := fun x => HilbertVec.ofVec (v.grad x)
    grad := fun x j => HilbertVec.ofVec (fun i => H.hess i j x)
    memL2 := ?_
    gradMemL2 := ?_
    hasWeakGradient := ?_ }
  · exact memHilbertVectorL2_hilbertifyVecField v.grad_memVectorL2
  · intro j
    apply memHilbertVectorL2_hilbertifyVecField
    apply (MeasureTheory.memLp_pi_iff).2
    intro i
    exact H.hess_memL2 i j
  · intro e
    let w : H1Function (openCubeSet Q) :=
      ∑ i : Fin 2, e.toVec i • H.gradCoordH1Function i
    have hval : (fun x => inner ℝ e (HilbertVec.ofVec (v.grad x))) = w.toFun := by
      funext x
      rw [HilbertVec.inner_def]
      simp [v, w, vecDot, Fin.sum_univ_two]
    have hgrad (j : Fin 2) :
        (fun x => inner ℝ e (HilbertVec.ofVec (fun i => H.hess i j x))) =
          fun x => w.grad x j := by
      funext x
      rw [HilbertVec.inner_def]
      simp [w, vecDot, Fin.sum_univ_two]
    rw [hval]
    convert w.hasWeakGradient using 1
    funext x j
    exact congrFun (hgrad j) x

end ASDExplicitGamma.Scalar
