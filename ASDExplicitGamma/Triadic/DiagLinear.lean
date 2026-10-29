module

public import ASDExplicitGamma.Triadic.DiagZeroTrace
public import ASDExplicitGamma.Variational.LemmaVMinimizer

/-! Linear mean-gradient and cell-mean maps for the DIAG interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

local instance diagFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The canonical affine slope used for all H¹ inputs. -/
def diagMeanGradientLinear (Q : TriadicCube 2) :
    H1Function (openCubeSet Q) →ₗ[ℝ] Vec 2 where
  toFun v := cubeAverageVec Q v.grad
  map_add' u v := by
    funext i
    simp only [cubeAverageVec, H1Function.add_grad, Pi.add_apply,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_add ((u.grad_memL2_normalizedCubeMeasure i).integrable one_le_two)
      ((v.grad_memL2_normalizedCubeMeasure i).integrable one_le_two)
  map_smul' c v := by
    funext i
    simp only [cubeAverageVec, H1Function.smul_grad, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, cubeAverage_eq_integral_normalizedCubeMeasure, integral_const_mul]

/-- Affine functions as a linear map into the explicit H¹ carrier. -/
def diagAffineLinear (Q : TriadicCube 2) : Vec 2 →ₗ[ℝ] H1Function (openCubeSet Q) where
  toFun p := H1Function.affineOnIsSobolevRegularDomain
    (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain p
  map_add' p q := by
    apply H1Function.ext
    · funext x
      simp only [H1Function.add_toFun, Pi.add_apply,
        H1Function.affineOnIsSobolevRegularDomain_apply, add_mul, Finset.sum_add_distrib]
    · funext x i
      simp only [H1Function.add_grad, Pi.add_apply,
        H1Function.affineOnIsSobolevRegularDomain_grad]
  map_smul' c p := by
    apply H1Function.ext
    · funext x
      simp only [H1Function.smul_toFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        H1Function.affineOnIsSobolevRegularDomain_apply, mul_assoc, Finset.mul_sum]
    · funext x i
      simp only [H1Function.smul_grad, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        H1Function.affineOnIsSobolevRegularDomain_grad]

/-- Removing the mean-gradient affine function is linear on all of H¹. -/
def diagResidualLinear (Q : TriadicCube 2) :
    H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q) :=
  LinearMap.id - (diagAffineLinear Q).comp (diagMeanGradientLinear Q)

/-- A local cell mean is a linear functional on the parent H¹ carrier. -/
def diagCellMeanLinear (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (hR : R ∈ descendantsAtDepth Q j) : H1Function (openCubeSet Q) →ₗ[ℝ] ℝ where
  toFun v := cubeAverage R v.toFun
  map_add' u v := by
    simp only [H1Function.add_toFun, cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_add
      ((memLp_on_descendant_of_memLp hR u.memL2_normalizedCubeMeasure).integrable one_le_two)
      ((memLp_on_descendant_of_memLp hR v.memL2_normalizedCubeMeasure).integrable one_le_two)
  map_smul' c v := by
    simp only [H1Function.smul_toFun, smul_eq_mul, RingHom.id_apply,
      cubeAverage_eq_integral_normalizedCubeMeasure, integral_const_mul]

/-- The actual triadic conditional mean field, evaluated as a linear map. -/
def diagProjectionLinear (Q : TriadicCube 2) (j : ℕ) :
    H1Function (openCubeSet Q) →ₗ[ℝ] (Vec 2 → ℝ) := by
  classical
  exact ∑ R ∈ (descendantsAtDepth Q j).attach,
    (LinearMap.pi fun x => if x ∈ cubeSet R.val then diagCellMeanLinear Q j R.val R.property else 0)

theorem diagProjectionLinear_apply (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (x : Vec 2) :
    diagProjectionLinear Q j v x = cubeProjection Q j v.toFun x := by
  classical
  simp only [diagProjectionLinear, LinearMap.sum_apply, LinearMap.pi_apply, Finset.sum_apply,
    cubeProjection]
  calc
    _ = ∑ R ∈ (descendantsAtDepth Q j).attach,
        if x ∈ cubeSet R.val then cubeAverage R.val v.toFun else 0 := by
      apply Finset.sum_congr rfl
      intro R _
      split_ifs <;> rfl
    _ = _ := Finset.sum_attach (descendantsAtDepth Q j)
      (fun R : TriadicCube 2 => if x ∈ cubeSet R then cubeAverage R v.toFun else 0)

/-- The design slope recovers the exact affine load, by the zero mean
of the gradient of the H¹₀ correction. -/
theorem diagMeanGradient_affinePotential (Q : TriadicCube 2) (p : Vec 2)
    (r : H10Function (openCubeSet Q)) :
    diagMeanGradientLinear Q
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r) = p := by
  funext i
  change cubeAverage Q (fun x =>
    ((diagAffineLinear Q p).grad x i + r.toH1Function.grad x i)) = p i
  simp only [diagAffineLinear, LinearMap.coe_mk, AddHom.coe_mk,
    H1Function.affineOnIsSobolevRegularDomain_grad]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_add (integrable_const _) ((r.toH1Function.grad_memL2_normalizedCubeMeasure i).integrable one_le_two)]
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q (fun x => r.toH1Function.grad x i),
    cubeAverage_h10_gradient_eq_zero]
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q (fun _ => p i)]
  simpa only [add_zero] using cubeAverage_const Q (p i)

end

end ASDExplicitGamma.Triadic
