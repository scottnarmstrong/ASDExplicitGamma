module

public import ASDExplicitGamma.Scalar.Lambda8LoadInputs
public import ASDExplicitGamma.Triadic.HilbertHaarAlgebra
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1

/-! Cellwise positive-Haar control for the actual parent Dirichlet projection. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- The gradient of an H¹ function with an L² weak Hessian is a genuine
Hilbert-valued H¹ field. -/
noncomputable def lambda8HessianGradientH1OfH1 (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u) :
    HilbertH1Function (openCubeSet Q) (HilbertVec 2) := by
  refine {
    toFun := fun x => HilbertVec.ofVec (u.grad x)
    grad := fun x j => HilbertVec.ofVec (fun i => H.hess i j x)
    memL2 := ?_
    gradMemL2 := ?_
    hasWeakGradient := ?_ }
  · exact memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2
  · intro j
    apply memHilbertVectorL2_hilbertifyVecField
    apply (MeasureTheory.memLp_pi_iff).2
    intro i
    exact H.hess_memL2 i j
  · intro e
    let w : H1Function (openCubeSet Q) :=
      ∑ i : Fin 2, e.toVec i • H.gradCoordH1Function i
    have hval : (fun x => inner ℝ e (HilbertVec.ofVec (u.grad x))) = w.toFun := by
      funext x
      rw [HilbertVec.inner_def]
      simp [w, vecDot, Fin.sum_univ_two]
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

/-- A generic H¹ potential's positive quarter-order gradient oscillation is
controlled by its weak Hessian on the same square. -/
theorem lambda8_h1_hessian_gradient_positive_circ_sq_le (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u) :
    hilbertPositiveCircHaarNorm Q ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec (u.grad x)) ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
        (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x)) := by
  have hp := hilbert_positive_circ_poincare_norm Q (1 / 4 : ℝ)
    ⟨by norm_num, by norm_num⟩ (lambda8HessianGradientH1OfH1 Q u H)
  have hsum_nonneg : 0 ≤ ∑ j : Fin 2, ∑ i : Fin 2,
      energy Q (fun x => H.hess i j x) :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hright_nonneg : 0 ≤ cubeScaleFactor Q * planarC0 *
      Real.sqrt (∑ j : Fin 2, ∑ i : Fin 2, energy Q (fun x => H.hess i j x)) :=
    mul_nonneg (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
      (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hgrad : hilbertGradientEnergy Q
      (fun x j => HilbertVec.ofVec (fun i => H.hess i j x)) =
      ∑ j : Fin 2, ∑ i : Fin 2, energy Q (fun x => H.hess i j x) := by
    unfold hilbertGradientEnergy
    apply Finset.sum_congr rfl
    intro j hj
    rw [hilbertEnergy]
    change ∫ x, ‖HilbertVec.ofVec (fun i => H.hess i j x)‖ ^ 2
        ∂normalizedCubeMeasure Q =
      ∑ i : Fin 2, energy Q (fun x => H.hess i j x)
    have hInt (i : Fin 2) :
        Integrable (fun x => (H.hess i j x) ^ 2) (normalizedCubeMeasure Q) := by
      have hm := H.hess_memLp_normalizedCubeMeasure Q i j
      have hi := hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
      simpa only [Real.norm_eq_abs, sq_abs] using hi
    simp_rw [HilbertVec.norm_sq_eq_sum_sq]
    rw [integral_finsetSum _ (fun i _ => hInt i)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [energy_eq_integral_sq]
  have hp' : hilbertPositiveCircHaarNorm Q ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
      (fun x => HilbertVec.ofVec (u.grad x)) ≤
      cubeScaleFactor Q * Real.sqrt (haarPoincareC2 ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))) *
        Real.sqrt (hilbertGradientEnergy Q
          (fun x j => HilbertVec.ofVec (fun i => H.hess i j x))) := by
    simpa [lambda8HessianGradientH1OfH1] using hp
  rw [haarPoincareC2_quarter, hgrad] at hp'
  have hc0 : Real.sqrt (planarC0 ^ 2) = planarC0 :=
    Real.sqrt_sq (Real.sqrt_nonneg _)
  rw [hc0] at hp'
  have hpc : 0 ≤ hilbertPrimalCircEnergy Q ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
      (fun x => HilbertVec.ofVec (u.grad x)) := by
    unfold hilbertPrimalCircEnergy
    apply tsum_nonneg
    intro k
    exact mul_nonneg (pow_nonneg (by positivity) _) (hilbertEnergy_nonneg Q _)
  rw [hilbertPositiveCircHaarNorm] at hp'
  have hpSq := (sq_le_sq₀ (Real.sqrt_nonneg _) hright_nonneg).2 hp'
  rw [Real.sq_sqrt hpc, mul_pow, Real.sq_sqrt hsum_nonneg] at hpSq
  have hnormsq : hilbertPositiveCircHaarNorm Q ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
      (fun x => HilbertVec.ofVec (u.grad x)) ^ 2 =
        hilbertPrimalCircEnergy Q ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
          (fun x => HilbertVec.ofVec (u.grad x)) := by
    rw [hilbertPositiveCircHaarNorm, Real.sq_sqrt hpc]
  calc
    _ = hilbertPrimalCircEnergy Q ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec (u.grad x)) := hnormsq
    _ ≤ (cubeScaleFactor Q * planarC0) ^ 2 *
        ∑ j : Fin 2, ∑ i : Fin 2, energy Q (fun x => H.hess i j x) := hpSq
    _ = cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
        ∑ j : Fin 2, ∑ i : Fin 2, energy Q (fun x => H.hess i j x) := by ring
    _ = cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
        ∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x) := by
      rw [Finset.sum_comm]

/-- The quarter-order oscillation of a parent-square Dirichlet gradient,
averaged over any fixed descendant generation, is controlled by its parent
Hessian energy. The Hessian identity is not localized to the descendant cells. -/
theorem lambda8_parentProjection_descendant_oscillation_sq_le
    (Q : TriadicCube 2) (n : ℕ)
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    descendantsAverage Q n (fun R =>
      hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec (u.toH1Function.grad x)) ^ 2) ≤
      cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2 *
        energy Q (dirichletWeakLaplacian H) := by
  have hcell : ∀ R ∈ descendantsAtDepth Q n,
      hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (fun x => HilbertVec.ofVec (u.toH1Function.grad x)) ^ 2 ≤
        cubeScaleFactor R ^ 2 * planarC0 ^ 2 *
          (∑ i : Fin 2, ∑ j : Fin 2,
            energy R (fun x => H.hess i j x)) := by
    intro R hR
    let hopen := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let uR := u.toH1Function.restrict (isOpen_openCubeSet R) hopen
    let HR := H.restrict (isOpen_openCubeSet R) hopen
    have hbase := lambda8_h1_hessian_gradient_positive_circ_sq_le R uR HR
    simpa [uR, HR, H1Function.restrict, HasWeakHessianOn.restrict] using hbase
  have havg := descendantsAverage_le hcell
  have hHess : ∀ i j : Fin 2,
      MemLp (fun x => H.hess i j x) 2 (normalizedCubeMeasure Q) := by
    intro i j
    exact H.hess_memLp_normalizedCubeMeasure Q i j
  have havgHess : ∀ i j : Fin 2,
      descendantsAverage Q n (fun R => energy R (fun x => H.hess i j x)) =
        energy Q (fun x => H.hess i j x) := by
    intro i j
    exact (energy_eq_descendantsAverage Q n (hHess i j)).symm
  have hscale (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q n) :
      cubeScaleFactor R ^ 2 = cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n := by
    rw [cubeScaleFactor_descendant_eq_div_pow hR, div_pow]
    have h9 : ((3 : ℝ) ^ n) ^ 2 = (9 : ℝ) ^ n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    rw [h9]
  have hconst :
      descendantsAverage Q n (fun R => cubeScaleFactor R ^ 2 * planarC0 ^ 2 *
        (∑ i : Fin 2, ∑ j : Fin 2, energy R (fun x => H.hess i j x))) =
      (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
        descendantsAverage Q n (fun R => ∑ i : Fin 2, ∑ j : Fin 2,
          energy R (fun x => H.hess i j x)) := by
    let D := descendantsAtDepth Q n
    change (D.card : ℝ)⁻¹ * D.sum (fun R => cubeScaleFactor R ^ 2 * planarC0 ^ 2 *
        (∑ i : Fin 2, ∑ j : Fin 2, energy R (fun x => H.hess i j x))) =
      (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
        ((D.card : ℝ)⁻¹ * D.sum (fun R =>
          ∑ i : Fin 2, ∑ j : Fin 2, energy R (fun x => H.hess i j x)))
    have hsum : D.sum (fun R => cubeScaleFactor R ^ 2 * planarC0 ^ 2 *
        (∑ i : Fin 2, ∑ j : Fin 2, energy R (fun x => H.hess i j x))) =
      (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
        D.sum (fun R => ∑ i : Fin 2, ∑ j : Fin 2,
          energy R (fun x => H.hess i j x)) := by
      calc
        _ = D.sum (fun R => (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
            (∑ i : Fin 2, ∑ j : Fin 2, energy R (fun x => H.hess i j x))) := by
          apply Finset.sum_congr rfl
          intro R hR
          rw [hscale R hR]
        _ = _ := by rw [Finset.mul_sum]
    rw [hsum]
    ring
  have hsum :
      (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x)) =
        energy Q (dirichletWeakLaplacian H) := by
    have hcoord (i j : Fin 2) :
        energy Q (fun x => H.hess i j x) =
          (cubeVolume Q)⁻¹ * ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
      rw [energy_eq_integral_sq, H.integral_hess_sq_normalizedCubeMeasure Q]
    have hfrob :
        (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x)) =
          H.frobeniusNormalizedL2 Q ^ 2 := by
      calc
        _ = ∑ i : Fin 2, ∑ j : Fin 2,
            (cubeVolume Q)⁻¹ * ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
          simp_rw [hcoord]
        _ = (cubeVolume Q)⁻¹ *
            ∑ i : Fin 2, ∑ j : Fin 2, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
          calc
            _ = ∑ i : Fin 2, (cubeVolume Q)⁻¹ *
                ∑ j : Fin 2, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]
        _ = _ := (H.frobeniusNormalizedL2_sq Q).symm
    calc
      _ = H.frobeniusNormalizedL2 Q ^ 2 := hfrob
      _ = (cubeLpNorm Q 2 (dirichletWeakLaplacian H)) ^ 2 := by
        rw [dirichlet_square_hessian_identity Q u H]
      _ = energy Q (dirichletWeakLaplacian H) :=
        (energy_eq_cubeLpNorm_sq Q (memLp_dirichlet_weak_laplacian H)).symm
  calc
    descendantsAverage Q n (fun R =>
        hilbertPositiveCircHaarNorm R ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
          (fun x => HilbertVec.ofVec (u.toH1Function.grad x)) ^ 2) ≤
      descendantsAverage Q n (fun R => cubeScaleFactor R ^ 2 * planarC0 ^ 2 *
        (∑ i : Fin 2, ∑ j : Fin 2, energy R (fun x => H.hess i j x))) := havg
    _ = (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
        descendantsAverage Q n (fun R => ∑ i : Fin 2, ∑ j : Fin 2,
          energy R (fun x => H.hess i j x)) := hconst
    _ = (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) *
        (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x)) := by
      rw [descendantsAverage_sum]
      apply congrArg (fun z : ℝ =>
        (cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2) * z)
      apply Finset.sum_congr rfl
      intro i hi
      rw [descendantsAverage_sum]
      simp_rw [havgHess]
    _ = cubeScaleFactor Q ^ 2 / (9 : ℝ) ^ n * planarC0 ^ 2 *
        energy Q (dirichletWeakLaplacian H) := by rw [hsum]

end
end ASDExplicitGamma.Scalar
