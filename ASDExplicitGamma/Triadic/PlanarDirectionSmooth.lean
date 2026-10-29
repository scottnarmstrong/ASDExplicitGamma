module

public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import ASDExplicitGamma.Triadic.DiagCoordinateHat
public import Homogenization.Sobolev.H1.BasicLemmas

/-! Canonical planar W^{2,∞} witnesses of actual globally C2 functions. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

 theorem continuous_memLp_top_normalized {d : ℕ} (Q : TriadicCube d) {f : Vec d → ℝ} (hf : Continuous f) :
    MemLp f ⊤ (normalizedCubeMeasure Q) := by
  obtain ⟨C,hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [hilbert_ae_cubeSet Q] with x hx
  exact hC x (subset_closure hx)

 def smoothCoordinateDerivative (f : Vec 2 → ℝ) (i : Fin 2) (x : Vec 2) : ℝ :=
  fderiv ℝ f x (basisVec i)

 theorem smoothCoordinateDerivative_contDiff {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 2) :
    ContDiff ℝ 1 (smoothCoordinateDerivative f i) :=
  (hf.fderiv_right (by norm_num)).clm_apply contDiff_const

/-- This constructor fixes the value, weak gradient and weak Hessian, rather than assuming a witness. -/
def PlanarW2Infinity.ofContDiff (Q : TriadicCube 2) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) : PlanarW2Infinity Q where
  value := H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q) (hf.of_le (by norm_num))
  value_memLp_top := diagContinuous_memLp_top Q hf.continuous
  gradient := {
    component := fun i => H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
      (smoothCoordinateDerivative_contDiff hf i)
    component_memLp_top := fun i => continuous_memLp_top_normalized Q (smoothCoordinateDerivative_contDiff hf i).continuous
    derivative_memLp_top := fun i j => continuous_memLp_top_normalized Q
      (((smoothCoordinateDerivative_contDiff hf i).continuous_fderiv (by norm_num)).clm_apply continuous_const) }
  gradient_eq _ := rfl

 theorem PlanarW2Infinity.ofContDiff_value (Q : TriadicCube 2) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) :
    (PlanarW2Infinity.ofContDiff Q f hf).value.toFun = f := rfl

 theorem PlanarW2Infinity.ofContDiff_grad (Q : TriadicCube 2) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (x : Vec 2) (i : Fin 2) :
    (PlanarW2Infinity.ofContDiff Q f hf).value.grad x i = smoothCoordinateDerivative f i x := rfl

 theorem PlanarW2Infinity.ofContDiff_hessian (Q : TriadicCube 2) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (x : Vec 2) (i j : Fin 2) :
    planarW1Derivative (PlanarW2Infinity.ofContDiff Q f hf).gradient x i j =
      fderiv ℝ (smoothCoordinateDerivative f i) x (basisVec j) := rfl

end
end ASDExplicitGamma.Triadic
