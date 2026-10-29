module

public import ASDExplicitGamma.Scalar.Lambda8LocalProjection
public import ASDExplicitGamma.Scalar.DirichletWeak
public import ASDExplicitGamma.Scalar.DirichletSquareHessian
public import ASDExplicitGamma.Triadic.PoincareCell

/-! The local Dirichlet projection of an H¹ vector load solves its divergence
Poisson equation. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory
open Triadic
open scoped BigOperators

/-- The vector field whose components are the supplied scalar H¹ functions. -/
def lambda8H1ComponentField {U : Set (Vec 2)}
    (F : Fin 2 → H1Function U) : Vec 2 → Vec 2 :=
  fun x i => F i x

/-- The weak divergence of the componentwise H¹ load. -/
def lambda8H1ComponentDivergence {U : Set (Vec 2)}
    (F : Fin 2 → H1Function U) (x : Vec 2) : ℝ :=
  ∑ i : Fin 2, (F i).grad x i

theorem lambda8H1ComponentField_memVectorL2 {Q : TriadicCube 2}
    (F : Fin 2 → H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q) (lambda8H1ComponentField F) := by
  apply (MeasureTheory.memLp_pi_iff).2
  intro i
  exact (F i).memL2

theorem lambda8H1ComponentDivergence_memLp (Q : TriadicCube 2)
    (F : Fin 2 → H1Function (openCubeSet Q)) :
    MemLp (lambda8H1ComponentDivergence F) 2 (normalizedCubeMeasure Q) := by
  apply memLp_normalized_of_memL2On
  change MemLp (fun x => ∑ i : Fin 2, (F i).grad x i) 2
    (volume.restrict (openCubeSet Q))
  apply MeasureTheory.memLp_finsetSum
  intro i _
  exact (F i).grad_memL2 i

private theorem lambda8_component_load_pairing (Q : TriadicCube 2)
    (F : Fin 2 → H1Function (openCubeSet Q))
    (φ : H10Function (openCubeSet Q)) :
    (∫ x in openCubeSet Q,
      vecDot (lambda8H1ComponentField F x) (φ.toH1Function.grad x)
      ∂volume) =
    -∫ x in openCubeSet Q,
      lambda8H1ComponentDivergence F x * φ.toH1Function x ∂volume := by
  have hprod (i : Fin 2) : Integrable
      (fun x => (F i) x * φ.toH1Function.grad x i)
      (volume.restrict (openCubeSet Q)) :=
    (F i).memL2.integrable_mul (φ.toH1Function.gradMemL2 i)
  have hsource (i : Fin 2) := weak_partial_test_H10
    (isOpen_openCubeSet Q) ((F i).hasWeakGradient i)
    (F i).memL2 ((F i).grad_memL2 i) φ
  rw [show (fun x => vecDot (lambda8H1ComponentField F x)
      (φ.toH1Function.grad x)) =
      fun x => ∑ i : Fin 2, (F i) x * φ.toH1Function.grad x i by
        funext x
        simp [vecDot, lambda8H1ComponentField]]
  rw [integral_finsetSum _ (fun i _ => hprod i)]
  simp_rw [hsource]
  rw [Finset.sum_neg_distrib]
  have hsum : (fun x => ∑ i : Fin 2, (F i).grad x i * φ.toH1Function x) =
      fun x => lambda8H1ComponentDivergence F x * φ.toH1Function x := by
    funext x
    simp [lambda8H1ComponentDivergence, Fin.sum_univ_two]
    ring
  have hdivSum :
      (∫ x in openCubeSet Q,
        ∑ i : Fin 2, (F i).grad x i * φ.toH1Function x ∂volume) =
      ∑ i : Fin 2, ∫ x in openCubeSet Q,
        (F i).grad x i * φ.toH1Function x ∂volume :=
    integral_finsetSum Finset.univ (fun i _ =>
      ((F i).grad_memL2 i).integrable_mul φ.toH1Function.memL2)
  calc
    -∑ i : Fin 2, ∫ x in openCubeSet Q,
        (F i).grad x i * φ.toH1Function x ∂volume =
      -∫ x in openCubeSet Q,
        lambda8H1ComponentDivergence F x * φ.toH1Function x ∂volume := by
          rw [← hdivSum, hsum]

/-- The orthogonal projection of the actual H¹ component load has the weak
Dirichlet Poisson equation with source minus its weak divergence. -/
theorem lambda8DirichletProjection_poisson (Q : TriadicCube 2)
    (F : Fin 2 → H1Function (openCubeSet Q)) :
    ∃ u : H10Function (openCubeSet Q),
      lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
        (toHilbertVectorL2OfVecField (lambda8H1ComponentField_memVectorL2 F)) =
          u.toH1Function.gradToHilbertVectorL2 ∧
      CubeDirichletWeakPoissonProblem Q u
        (fun x => -lambda8H1ComponentDivergence F x) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let f := lambda8H1ComponentField F
  let hf := lambda8H1ComponentField_memVectorL2 F
  let FH := toHilbertVectorL2OfVecField hf
  obtain ⟨u, hu⟩ := lambda8DirichletProjection_isPotentialZeroTrace hU FH
  refine ⟨u, hu.symm, ?_⟩
  intro φ
  have horth := lambda8DirichletProjection_residual_orthogonal hU FH φ
  have hpair := inner_toHilbertVectorL2OfVecField_eq_integral
    hf φ.toH1Function.grad_memVectorL2
  have hgrad := inner_toHilbertVectorL2OfVecField_eq_integral
    u.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
  change inner ℝ (toHilbertVectorL2OfVecField hf)
      φ.toH1Function.gradToHilbertVectorL2 = _ at hpair
  change inner ℝ u.toH1Function.gradToHilbertVectorL2
      φ.toH1Function.gradToHilbertVectorL2 = _ at hgrad
  have hproj :
      inner ℝ (toHilbertVectorL2OfVecField hf)
        φ.toH1Function.gradToHilbertVectorL2 =
      inner ℝ (lambda8DirichletProjection hU FH)
        φ.toH1Function.gradToHilbertVectorL2 := by
    rw [inner_sub_left] at horth
    linarith only [horth]
  rw [hu.symm, hpair, hgrad] at hproj
  calc
    (∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume) =
      (∫ x in openCubeSet Q,
        vecDot (lambda8H1ComponentField F x) (φ.toH1Function.grad x) ∂volume) :=
          hproj.symm
    _ = -∫ x in openCubeSet Q,
        lambda8H1ComponentDivergence F x * φ.toH1Function x ∂volume :=
          lambda8_component_load_pairing Q F φ
    _ = ∫ x in openCubeSet Q,
        (-lambda8H1ComponentDivergence F x) * φ.toH1Function x ∂volume := by
          simp_rw [neg_mul]
          rw [← integral_neg]

end ASDExplicitGamma.Scalar
