module

public import ASDExplicitGamma.Scalar.FlatSourceC1Multiplier
public import ASDExplicitGamma.Scalar.FlatSourceQ3LpBridge
public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation
public import ASDExplicitGamma.Main.CMRegularity
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1
public import Homogenization.Book.Ch02.MultiscaleEllipticity

/-! Finite q3 source products have the expected weak spatial gradient. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Main
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

/-- The finite q3 scalar field in the common white-noise coordinates. -/
noncomputable def flatSourceQ3FiniteScalar
    (β : ℝ) (L : {l : ℝ // 0 < l})
    (N : ℕ) (ω : ℕ → ℝ) : Vec 2 → ℝ := fun x =>
  gaussianScalarPartialSum
    (fun n => q3Convolution β L h3Zero (gaussEnumerated whiteBasis n) x)
    N ω

/-- A finite projected-load component as an actual H¹ function. Each mode is
the matching coordinate derivative of the parent potential, and its weak
gradient is the corresponding Hessian row. -/
noncomputable def flatSourceQ3FiniteProjectedComponent
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) :
    H1Function (openCubeSet Q) := by
  let modes : whiteBasisIndex → H1Function (openCubeSet Q) := fun j =>
    (lambda8Q3GaussianModeParentHessian Q β L
      (matVecMul responsePlanarJ e) j).gradCoordH1Function i
  exact ∑ n ∈ Finset.range N, ω n • gaussEnumerated modes n

/-- The finite q3 scalar times the finite projected-load component, with its
weak product gradient. The scalar and load retain their common Gaussian
coordinates. -/
noncomputable def flatSourceQ3FiniteProductComponent
    (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (e : Vec 2)
    (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) :
    H1Function (openCubeSet Q) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let φ := flatSourceQ3FiniteScalar β L N ω
  let u := flatSourceQ3FiniteProjectedComponent Q β L e N ω i
  have hφ : ContDiff ℝ 1 φ := by
    change ContDiff ℝ 1 (fun x =>
      ∑ n ∈ Finset.range N, ω n *
        q3Convolution β L h3Zero (gaussEnumerated whiteBasis n) x)
    apply ContDiff.sum
    intro n hn
    have hnC3 : ContDiff ℝ 3
        (q3Convolution β L h3Zero (gaussEnumerated whiteBasis n)) :=
      main_q3_value_direction_contDiff_three β L (gaussEnumerated whiteBasis n)
    exact (contDiff_const.mul hnC3).of_le (by norm_num)
  have htop := contDiffOne_memLpTop_of_bounded_open_domain hU hφ
  exact h1_mul_contDiffOne_memLpTop hU (Book.Ch02.openCubeSet_nonempty Q)
    u hφ htop.1 htop.2

theorem flat_source_q3_finite_product_component_toFun
    (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (e : Vec 2)
    (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) :
    (flatSourceQ3FiniteProductComponent Q β L e N ω i).toFun =
      fun x => flatSourceQ3FiniteScalar β L N ω x *
        flatSourceQ3FiniteProjectedComponent Q β L e N ω i x := by
  rfl

theorem flat_source_q3_finite_product_component_grad
    (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (e : Vec 2)
    (N : ℕ) (ω : ℕ → ℝ) (i j : Fin 2) (x : Vec 2) :
    (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j =
      flatSourceQ3FiniteScalar β L N ω x *
        (flatSourceQ3FiniteProjectedComponent Q β L e N ω i).grad x j +
      (flatSourceQ3FiniteProjectedComponent Q β L e N ω i).toFun x *
        (fderiv ℝ (flatSourceQ3FiniteScalar β L N ω) x) (basisVec j) := by
  rfl

end ASDExplicitGamma.Scalar
