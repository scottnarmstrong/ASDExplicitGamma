module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Basic

/-! The exact finite Hilbert tensor multiplier used by covariance columns. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open scoped BigOperators

/-- Literal tensor coordinates. -/
noncomputable def mainEuclideanTensor {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) (v : EuclideanSpace ℝ ρ) : EuclideanSpace ℝ (κ × ρ) :=
  WithLp.toLp 2 (fun p => a.ofLp p.1*v.ofLp p.2)

/-- Hilbert norms multiply exactly, avoiding a coordinate-count loss. -/
theorem mainEuclideanTensor_norm {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) (v : EuclideanSpace ℝ ρ) :
    ‖mainEuclideanTensor a v‖ = ‖a‖*‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [EuclideanSpace.real_norm_sq_eq, mainEuclideanTensor,
    mul_pow, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- A fixed Hilbert column acts on the spatial vector by its literal tensor. -/
noncomputable def mainEuclideanTensorOperator {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) : EuclideanSpace ℝ ρ →L[ℝ] EuclideanSpace ℝ (κ × ρ) :=
  LinearMap.mkContinuous
    { toFun := mainEuclideanTensor a
      map_add' := by intro u v; ext p; simp [mainEuclideanTensor]; ring
      map_smul' := by intro c v; ext p; simp [mainEuclideanTensor]; ring }
    ‖a‖ (fun v => (mainEuclideanTensor_norm a v).le)

/-- Tensor multiplication has operator norm at most the exact column norm. -/
theorem mainEuclideanTensorOperator_norm_le {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) : ‖mainEuclideanTensorOperator (ρ := ρ) a‖ ≤ ‖a‖ := by
  unfold mainEuclideanTensorOperator
  exact LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _

/-- Tensor multiplication is itself bounded linear in its coefficient column. -/
noncomputable def mainEuclideanTensorMap {κ ρ : Type*} [Fintype κ] [Fintype ρ] :
    EuclideanSpace ℝ κ →L[ℝ] (EuclideanSpace ℝ ρ →L[ℝ] EuclideanSpace ℝ (κ × ρ)) :=
  LinearMap.mkContinuous
    { toFun := mainEuclideanTensorOperator (κ := κ) (ρ := ρ)
      map_add' := by intro a b; ext v p; simp [mainEuclideanTensorOperator, mainEuclideanTensor]; ring
      map_smul' := by intro c a; ext v p; simp [mainEuclideanTensorOperator, mainEuclideanTensor]; ring }
    1 (fun a => by
      change ‖mainEuclideanTensorOperator (ρ := ρ) a‖ ≤ 1*‖a‖
      simpa only [one_mul] using mainEuclideanTensorOperator_norm_le (ρ := ρ) a)

end ASDExplicitGamma.Main
