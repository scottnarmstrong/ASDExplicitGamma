module

public import ASDExplicitGamma.Triadic.PlanarDirectionOperations

/-! Exact finite linear combinations of genuine H1 and planar W^{2,∞} witnesses. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

 def h1ValueLinearMap {d : ℕ} {U : Set (Vec d)} : H1Function U →ₗ[ℝ] (Vec d → ℝ) where
  toFun := H1Function.toFun
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 def h1GradCoordinateLinearMap {d : ℕ} {U : Set (Vec d)} (i : Fin d) : H1Function U →ₗ[ℝ] (Vec d → ℝ) where
  toFun u := fun x => u.grad x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem h1_finset_sum_toFun {d : ℕ} {U : Set (Vec d)} {ι : Type*}
    (η : ι → H1Function U) (s : Finset ι) (c : ι → ℝ) :
    (∑ l ∈ s, c l • η l).toFun = fun x => ∑ l ∈ s, c l*(η l).toFun x := by
  change h1ValueLinearMap (∑ l ∈ s, c l • η l) = _
  rw [map_sum]
  simp only [map_smul]
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1ValueLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

 theorem h1_finset_sum_grad {d : ℕ} {U : Set (Vec d)} {ι : Type*}
    (η : ι → H1Function U) (s : Finset ι) (c : ι → ℝ) (i : Fin d) :
    (fun x => (∑ l ∈ s, c l • η l).grad x i) = fun x => ∑ l ∈ s, c l*(η l).grad x i := by
  change h1GradCoordinateLinearMap i (∑ l ∈ s, c l • η l) = _
  rw [map_sum]
  simp only [map_smul]
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1GradCoordinateLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

 theorem h1_finset_sum_grad_apply {d : ℕ} {U : Set (Vec d)} {ι : Type*}
    (η : ι → H1Function U) (s : Finset ι) (c : ι → ℝ) (x : Vec d) (i : Fin d) :
    (∑ l ∈ s, c l • η l).grad x i = ∑ l ∈ s, c l*(η l).grad x i :=
  congrFun (h1_finset_sum_grad η s c i) x

 def PlanarW1Infinity.linearCombination {Q : TriadicCube 2} {ι : Type*}
    (η : ι → PlanarW1Infinity Q) (s : Finset ι) (c : ι → ℝ) : PlanarW1Infinity Q where
  component i := ∑ l ∈ s, c l • (η l).component i
  component_memLp_top i := by
    rw [h1_finset_sum_toFun]
    exact memLp_finsetSum s fun l _ => ((η l).component_memLp_top i).const_mul (c l)
  derivative_memLp_top i j := by
    rw [h1_finset_sum_grad]
    exact memLp_finsetSum s fun l _ => ((η l).derivative_memLp_top i j).const_mul (c l)

/-- The finite combination retains the actual value, weak gradient, and weak Hessian. -/
def PlanarW2Infinity.linearCombination {Q : TriadicCube 2} {ι : Type*}
    (η : ι → PlanarW2Infinity Q) (s : Finset ι) (c : ι → ℝ) : PlanarW2Infinity Q where
  value := ∑ l ∈ s, c l • (η l).value
  value_memLp_top := by
    rw [h1_finset_sum_toFun]
    exact memLp_finsetSum s fun l _ => (η l).value_memLp_top.const_mul (c l)
  gradient := PlanarW1Infinity.linearCombination (fun l => (η l).gradient) s c
  gradient_eq i := by
    change (∑ l ∈ s, c l • (η l).gradient.component i).toFun = _
    rw [h1_finset_sum_toFun, h1_finset_sum_grad]
    simp only [fun l => (η l).gradient_eq i]

end
end ASDExplicitGamma.Triadic
