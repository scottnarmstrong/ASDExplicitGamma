module

public import ASDExplicitGamma.Gaussian.MappedHeat

/-! # Cell centers, restrictions, and their joint remainder covariance -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

/-- Subtract evaluation at a deterministic center, as a bounded linear map on continuous fields. -/
def centeringMap {K : Type*} [TopologicalSpace K] [CompactSpace K] (x₀ : K) :
    C(K, ℝ) →L[ℝ] C(K, ℝ) :=
  ContinuousLinearMap.id ℝ _ - (ContinuousMap.evalCLM ℝ x₀).smulRight (1 : C(K, ℝ))

@[simp] theorem centeringMap_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (x₀ : K) (f : C(K, ℝ)) (x : K) : centeringMap x₀ f x = f x - f x₀ := by
  simp only [centeringMap, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one, ContinuousMap.evalCLM_apply]

/-- Restrict one common scalar field to a finite family of compact child sets. -/
def childRestrictionMap {n : ℕ} {K : Set (Vec 2)} [CompactSpace K]
    (U : Fin n → Set (Vec 2)) (hU : ∀ i, U i ⊆ K) :
    C(K, ℝ) →L[ℝ] (∀ i, C(U i, ℝ)) :=
  ContinuousLinearMap.pi fun i => ContinuousMap.compCLM ℝ ℝ
    ⟨fun x => ⟨x.1, hU i x.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- Separate constant fields are legitimate coefficients in the child product space. -/
def childConstantMap {n : ℕ} (U : Fin n → Set (Vec 2)) :
    (Fin n → ℝ) →L[ℝ] (∀ i, C(U i, ℝ)) :=
  ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i).smulRight (1 : C(U i, ℝ))

/-- The full joint vector of physical scalar center values. -/
def childCenterMap {n : ℕ} {K : Set (Vec 2)} [CompactSpace K] (x : Fin n → K) :
    C(K, ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousMap.evalCLM ℝ (x i)

/-- Center each child restriction using its own center in the common fresh field. -/
def childRemainderMap {n : ℕ} {K : Set (Vec 2)} [CompactSpace K]
    (U : Fin n → Set (Vec 2)) (hU : ∀ i, U i ⊆ K) (x : Fin n → K) :
    C(K, ℝ) →L[ℝ] (∀ i, C(U i, ℝ)) :=
  childRestrictionMap U hU - (childConstantMap U).comp (childCenterMap x)

@[simp] theorem childRemainderMap_apply {n : ℕ} {K : Set (Vec 2)} [CompactSpace K]
    (U : Fin n → Set (Vec 2)) (hU : ∀ i, U i ⊆ K) (x : Fin n → K)
    (f : C(K, ℝ)) (i : Fin n) (y : U i) :
    childRemainderMap U hU x f i y = f ⟨y.1, hU i y.2⟩ - f (x i) := by
  simp only [childRemainderMap, childRestrictionMap, childConstantMap, childCenterMap,
    sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    Pi.sub_apply, ContinuousMap.sub_apply, ContinuousMap.compCLM_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
    ContinuousMap.evalCLM_apply, smul_eq_mul, mul_one]

end ASDExplicitGamma.Gaussian
