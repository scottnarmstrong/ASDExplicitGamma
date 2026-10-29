module

public import ASDExplicitGamma.Scalar.ChaosCauchy

/-! Hilbert square-norm moments for vector-valued finite Gaussian second chaos.
Coordinate Cauchy--Schwarz needs no independence between the quadratic coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

/-- The squared Hilbert norm, in orthonormal coordinates, of a vector Gaussian quadratic. -/
noncomputable def finiteGaussianChaosNormSq {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, (centeredGaussianQuadratic (A i) x)^2

theorem gaussian_quadratic_square_product {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Integrable (fun x => (centeredGaussianQuadratic A x)^2*(centeredGaussianQuadratic B x)^2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, (centeredGaussianQuadratic A x)^2*(centeredGaussianQuadratic B x)^2
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      15*(∫ x, (centeredGaussianQuadratic A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))*
        (∫ x, (centeredGaussianQuadratic B x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have hc (C : Matrix (Fin n) (Fin n) ℝ) : Continuous (centeredGaussianQuadratic C) := by
    unfold centeredGaussianQuadratic
    fun_prop
  have h := square_product_cauchy _ _ _ (hc A).measurable.aestronglyMeasurable
    (hc B).measurable.aestronglyMeasurable
    (integrable_centered_gaussian_quadratic_power A hA 4) (integrable_centered_gaussian_quadratic_power B hB 4)
  have ha := centered_gaussian_quadratic_fourth_le_fifteen A hA
  have hb := centered_gaussian_quadratic_fourth_le_fifteen B hB
  have hvA : 0 ≤ ∫ x, (centeredGaussianQuadratic A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hvB : 0 ≤ ∫ x, (centeredGaussianQuadratic B x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    integral_nonneg (fun x => sq_nonneg _)
  refine ⟨h.1,h.2.trans ?_⟩
  calc
    _ ≤ Real.sqrt (15*(∫ x, (centeredGaussianQuadratic A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2)*
        Real.sqrt (15*(∫ x, (centeredGaussianQuadratic B x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2) :=
      mul_le_mul (Real.sqrt_le_sqrt ha) (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 15),Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 15),
        Real.sqrt_sq hvA,Real.sqrt_sq hvB]
      calc
        _ = (Real.sqrt 15)^2*(∫ x, (centeredGaussianQuadratic A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))*
            (∫ x, (centeredGaussianQuadratic B x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)]

/-- The sharp second-chaos estimate also holds for the squared norm of a vector quadratic. -/
theorem finite_gaussian_chaos_norm_fourth {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    (∫ x, (finiteGaussianChaosNormSq A x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      15*(∫ x, finiteGaussianChaosNormSq A x ∂stdGaussian (EuclideanSpace ℝ (Fin n)))^2 := by
  have hInt (i j : Fin d) := (gaussian_quadratic_square_product (A i) (A j) (hA i) (hA j)).1
  have hmean : (∫ x, finiteGaussianChaosNormSq A x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∑ i, ∫ x, (centeredGaussianQuadratic (A i) x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    integral_finsetSum _ (fun i _ => integrable_centered_gaussian_quadratic_power (A i) (hA i) 2)
  have he (x : EuclideanSpace ℝ (Fin n)) : (finiteGaussianChaosNormSq A x)^2 =
      ∑ i, ∑ j, (centeredGaussianQuadratic (A i) x)^2*(centeredGaussianQuadratic (A j) x)^2 := by
    simp only [finiteGaussianChaosNormSq,pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  simp_rw [he]
  rw [hmean,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt i j))]
  have hRow (i : Fin d) :
      (∫ x, ∑ j, (centeredGaussianQuadratic (A i) x)^2*(centeredGaussianQuadratic (A j) x)^2
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ∑ j, 15*(∫ x, (centeredGaussianQuadratic (A i) x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))*
        (∫ x, (centeredGaussianQuadratic (A j) x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
    rw [integral_finsetSum _ (fun j _ => hInt i j)]
    exact Finset.sum_le_sum (fun j _ => (gaussian_quadratic_square_product (A i) (A j) (hA i) (hA j)).2)
  calc
    _ ≤ ∑ i, ∑ j, 15*(∫ x, (centeredGaussianQuadratic (A i) x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n)))*
        (∫ x, (centeredGaussianQuadratic (A j) x)^2 ∂stdGaussian (EuclideanSpace ℝ (Fin n))) :=
      Finset.sum_le_sum (fun i _ => hRow i)
    _ = _ := by
      simp_rw [← Finset.mul_sum,← Finset.sum_mul]
      ring_nf
      rw [← Finset.sum_mul]
      ring

theorem integrable_finite_gaussian_chaos_norm_sq {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    Integrable (finiteGaussianChaosNormSq A) (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
  integrable_finsetSum _ (fun i _ => integrable_centered_gaussian_quadratic_power (A i) (hA i) 2)

theorem integrable_finite_gaussian_chaos_norm_fourth {d n : ℕ} (A : Fin d → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) :
    Integrable (fun x => (finiteGaussianChaosNormSq A x)^2) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have he : (fun x => (finiteGaussianChaosNormSq A x)^2) =
      fun x => ∑ i, ∑ j, (centeredGaussianQuadratic (A i) x)^2*(centeredGaussianQuadratic (A j) x)^2 := by
    funext x
    simp only [finiteGaussianChaosNormSq,pow_two,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    (gaussian_quadratic_square_product (A i) (A j) (hA i) (hA j)).1))

end ASDExplicitGamma.Scalar
