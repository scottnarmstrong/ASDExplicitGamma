module

public import ASDExplicitGamma.Scalar.DirichletDensity
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite sine approximations of arbitrary normalized square L2 forcing. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Triadic Torus MeasureTheory

/-- A sine mode with a zero frequency vanishes identically. -/
theorem dirichlet_mode_zero_frequency (Q : TriadicCube 2) (q : Fin 2 → ℕ)
    (hq : ¬∀ i,q i≠0) (x : Vec 2) : cubeDirichletMode Q q x=0 := by
  push Not at hq
  obtain ⟨i,hi⟩ := hq
  unfold cubeDirichletMode boxMode
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [natVec,hi]

/-- The finite polynomial represents the actual Hilbert-space linear combination. -/
theorem dirichlet_linear_combination_value (Q : TriadicCube 2)
    (c : (Fin 2 → ℕ) →₀ ℝ) :
    (c.linearCombination ℝ (dirichletModeL2 Q) : Vec 2 → ℝ) =ᵐ[normalizedCubeMeasure Q]
      dirichletPolynomial Q (c.support.filter (fun q => ∀ i,q i≠0)) c := by
  classical
  have hc := Lp.coeFn_linearCombination c (dirichletModeL2 Q)
  have hm : ∀ᵐ x ∂normalizedCubeMeasure Q,∀ q : Fin 2 → ℕ,
      (dirichletModeL2 Q q : Vec 2 → ℝ) x=cubeDirichletMode Q q x :=
    ae_all_iff.mpr (fun q => (memLp_dirichlet_mode Q q).coeFn_toLp)
  filter_upwards [hc,hm] with x hx hm
  rw [hx]
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,hm,dirichletPolynomial]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _) 
  intro q hq hnot
  have hz : ¬∀ i,q i≠0 := by simpa only [Finset.mem_filter,hq,true_and] using hnot
  rw [dirichlet_mode_zero_frequency Q q hz x,mul_zero]

/-- Every L2 function is a limit of genuine finite sine polynomials with positive frequencies. -/
theorem exists_dirichlet_polynomial_L2_approximation (Q : TriadicCube 2) (f : DirichletL2 Q) :
    ∃ (S : ℕ → Finset (Fin 2 → ℕ)) (β : ℕ → (Fin 2 → ℕ) → ℝ)
      (g : ℕ → DirichletL2 Q),
      (∀ n,∀ q ∈ S n,∀ i,q i≠0) ∧
      (∀ n,(g n : Vec 2 → ℝ) =ᵐ[normalizedCubeMeasure Q] dirichletPolynomial Q (S n) (β n)) ∧
      Filter.Tendsto g Filter.atTop (nhds f) := by
  classical
  have hd : f ∈ closure (Submodule.span ℝ (Set.range (dirichletModeL2 Q)) : Set (DirichletL2 Q)) := by
    rw [← Submodule.topologicalClosure_coe,dirichlet_sine_span_dense]
    trivial
  obtain ⟨g,hg,hlim⟩ := mem_closure_iff_seq_limit.mp hd
  have hc (n : ℕ) := Finsupp.mem_span_range_iff_exists_finsupp.mp (hg n)
  choose c hc using hc
  refine ⟨fun n => (c n).support.filter (fun q => ∀ i,q i≠0),fun n => c n,g,?_,?_,hlim⟩
  · intro n q hq
    exact (Finset.mem_filter.mp hq).2
  · intro n
    have h := dirichlet_linear_combination_value Q (c n)
    have he : (c n).linearCombination ℝ (dirichletModeL2 Q)=g n := hc n
    rw [he] at h
    exact h

end ASDExplicitGamma.Scalar
