/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Bases
import Mathlib.Topology.NhdsWithin

/-!
# Hilbert factorization of summable continuous families
-/

@[expose] public section

open scoped ENNReal

universe u

namespace ASDExplicitGamma.Gaussian

/-- The real Hilbert space of square-summable sequences used for the factorization. -/
abbrev GaussianFactorL2 (ι : Type u) := lp (fun _ : ι => ℝ) 2

private noncomputable def factorWeight {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (j : ι) : ℝ := ‖H j‖

private noncomputable def factorNormalized {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (j : ι) : C(K, ℝ) :=
  (Real.sqrt (factorWeight H j))⁻¹ • H j

private theorem factorNormalized_norm_le {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (j : ι) :
    ‖factorNormalized H j‖ ≤ Real.sqrt (factorWeight H j) := by
  unfold factorNormalized factorWeight
  have hw : 0 ≤ ‖H j‖ := norm_nonneg _
  by_cases hz : ‖H j‖ = 0
  · simp [hz]
  · have hp : 0 < ‖H j‖ := lt_of_le_of_ne hw (Ne.symm hz)
    have hs : 0 < Real.sqrt ‖H j‖ := Real.sqrt_pos.2 hp
    calc
      ‖(Real.sqrt ‖H j‖)⁻¹ • H j‖ = |(Real.sqrt ‖H j‖)⁻¹| * ‖H j‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = (Real.sqrt ‖H j‖)⁻¹ * ‖H j‖ := by
        rw [abs_of_nonneg (inv_nonneg.mpr hs.le)]
      _ ≤ Real.sqrt ‖H j‖ := by
        suffices (Real.sqrt ‖H j‖)⁻¹ * ‖H j‖ = Real.sqrt ‖H j‖ by rw [this]
        field_simp
        rw [Real.sq_sqrt hw]

private noncomputable def factorSqrtWeights {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (hH : Summable (fun j => ‖H j‖)) : GaussianFactorL2 ι := by
  refine ⟨fun j => Real.sqrt (factorWeight H j), ?_⟩
  apply memℓp_gen
  have hsum : Summable (fun j => (Real.sqrt (factorWeight H j)) ^ 2) := by
    convert hH using 1
    funext j
    simp [factorWeight, Real.sq_sqrt (norm_nonneg (H j))]
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hsum

private theorem factor_product_summable {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (hH : Summable (fun j => ‖H j‖)) (a : GaussianFactorL2 ι) :
    Summable (fun j => |a j| * Real.sqrt (factorWeight H j)) := by
  have hmul := lp.tsum_mul_le_mul_norm
    (by rw [Real.holderConjugate_iff]; norm_num :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal)
      a (factorSqrtWeights H hH)
  convert hmul.1 using 1
  funext j
  simp [factorSqrtWeights, factorWeight, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

private theorem factorTerm_summable {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (hH : Summable (fun j => ‖H j‖)) (a : GaussianFactorL2 ι) :
    Summable (fun j => a j • factorNormalized H j) := by
  apply Summable.of_norm_bounded (factor_product_summable H hH a)
  intro j
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (factorNormalized_norm_le H j)
    (abs_nonneg _)

private noncomputable def factorLinearMap {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (hH : Summable (fun j => ‖H j‖)) :
    GaussianFactorL2 ι →ₗ[ℝ] C(K, ℝ) where
  toFun a := ∑' j, a j • factorNormalized H j
  map_add' a b := by
    calc
      ∑' j, (a + b) j • factorNormalized H j =
          ∑' j, (a j • factorNormalized H j + b j • factorNormalized H j) := by
            congr 1
            funext j
            simp [add_smul]
      _ = (∑' j, a j • factorNormalized H j) +
          ∑' j, b j • factorNormalized H j :=
            Summable.tsum_add (factorTerm_summable H hH a)
              (factorTerm_summable H hH b)
  map_smul' c a := by
    calc
      ∑' j, (c • a) j • factorNormalized H j =
          ∑' j, c • (a j • factorNormalized H j) := by
            congr 1
            funext j
            simp [lp.coeFn_smul, smul_smul]
      _ = c • (∑' j, a j • factorNormalized H j) :=
            (factorTerm_summable H hH a).tsum_const_smul c

private theorem factorLinearMap_norm_le {ι : Type*} [DecidableEq ι] [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (hH : Summable (fun j => ‖H j‖)) (a : GaussianFactorL2 ι) :
    ‖factorLinearMap H hH a‖ ≤ ‖factorSqrtWeights H hH‖ * ‖a‖ := by
  calc
    _ ≤ ∑' j, |a j| * Real.sqrt (factorWeight H j) :=
      tsum_of_norm_bounded (factor_product_summable H hH a).hasSum (fun j => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (factorNormalized_norm_le H j)
          (abs_nonneg _))
    _ ≤ ‖a‖ * ‖factorSqrtWeights H hH‖ := by
      have hCS := (lp.tsum_mul_le_mul_norm
        (by rw [Real.holderConjugate_iff]; norm_num :
          (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal)
        a (factorSqrtWeights H hH)).2
      convert hCS using 1
      congr 1
      funext j
      simp [factorSqrtWeights, factorWeight, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    _ = ‖factorSqrtWeights H hH‖ * ‖a‖ := by ring

private noncomputable def gaussianFactorRationalVector
    (p : Σ s : Finset ℕ, (↥s → ℚ)) : GaussianFactorL2 ℕ :=
  p.1.attach.sum fun i => lp.single 2 (i : ℕ) ((p.2 i : ℚ) : ℝ)

private noncomputable def gaussianFactorFiniteRealVector (s : Finset ℕ)
    (a : ↥s → ℝ) : GaussianFactorL2 ℕ :=
  s.attach.sum fun i => lp.single 2 (i : ℕ) (a i)

private theorem gaussianFactorFiniteRealVector_mem_closure_rational
    (s : Finset ℕ) (a : ↥s → ℝ) :
    gaussianFactorFiniteRealVector s a ∈ closure (Set.range gaussianFactorRationalVector) := by
  let g : (↥s → ℚ) → (↥s → ℝ) := fun q i => (q i : ℝ)
  have hg : DenseRange g := DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hF : Continuous (gaussianFactorFiniteRealVector s) := by
    apply continuous_finsetSum
    intro i hi
    exact (lp.singleContinuousLinearMap ℝ (fun _ : ℕ => ℝ) 2 i).continuous.comp
      (continuous_apply i)
  have ha : a ∈ closure (Set.range g) := by rw [hg.closure_eq]; exact Set.mem_univ a
  have hcontAt : ContinuousAt (gaussianFactorFiniteRealVector s) a :=
    (continuous_iff_continuousAt.mp hF) a
  have hmem := mem_closure_image hcontAt ha
  apply closure_mono ?_ hmem
  rintro y ⟨a', ha', rfl⟩
  rcases ha' with ⟨q, rfl⟩
  refine ⟨⟨s, q⟩, ?_⟩
  simp [gaussianFactorFiniteRealVector, gaussianFactorRationalVector, g]

/-- Real `ℓ²` on `ℕ` is second-countable. Its dense subset consists of finitely-supported rational
sequences. -/
instance gaussianFactorL2NatSecondCountable :
    SecondCountableTopology (GaussianFactorL2 ℕ) := by
  have hDense : DenseRange gaussianFactorRationalVector := by
    rw [DenseRange, dense_iff_closure_eq]
    ext x
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      have hs : HasSum (fun i : ℕ => lp.single 2 i (x i)) x :=
        lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x
      apply IsClosed.mem_of_tendsto isClosed_closure hs.tendsto_sum_nat
        (Filter.Eventually.of_forall fun n => ?_)
      simpa [gaussianFactorFiniteRealVector] using
        gaussianFactorFiniteRealVector_mem_closure_rational (Finset.range n) (fun i => x i)
  have hSeparable : TopologicalSpace.SeparableSpace (GaussianFactorL2 ℕ) :=
    ⟨⟨Set.range gaussianFactorRationalVector, Set.countable_range _, hDense⟩⟩
  exact @UniformSpace.secondCountable_of_separable (GaussianFactorL2 ℕ) _ _ hSeparable

noncomputable instance gaussianFactorL2NatMeasurableSpace :
    MeasurableSpace (GaussianFactorL2 ℕ) := borel (GaussianFactorL2 ℕ)

noncomputable instance gaussianFactorL2NatBorelSpace : BorelSpace (GaussianFactorL2 ℕ) where
  measurable_eq := rfl

/-- A summable family of continuous functions factors through real `ℓ²`: the factor vectors have
square-summable norms and the bounded operator sends each factor vector to the corresponding
continuous function. -/
theorem exists_l2_factorization_of_summable_norm {ι : Type*} [Countable ι]
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ι → C(K, ℝ)) (hH : Summable (fun j => ‖H j‖)) :
    ∃ (T : GaussianFactorL2 ι →L[ℝ] C(K, ℝ)) (v : ι → GaussianFactorL2 ι),
      Summable (fun j => ‖v j‖ ^ 2) ∧ ∀ j, T (v j) = H j := by
  classical
  let v : ι → GaussianFactorL2 ι := fun j =>
    Real.sqrt (factorWeight H j) • lp.single 2 j (1 : ℝ)
  let L := factorLinearMap H hH
  let T : GaussianFactorL2 ι →L[ℝ] C(K, ℝ) := L.mkContinuous ‖factorSqrtWeights H hH‖
    (factorLinearMap_norm_le H hH)
  refine ⟨T, v, ?_, ?_⟩
  · have hv (j : ι) : ‖v j‖ ^ 2 = ‖H j‖ := by
      dsimp [v]
      simp [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), norm_one,
        factorWeight, Real.sq_sqrt (norm_nonneg (H j))]
    exact hH.congr (fun j => (hv j).symm)
  · intro j
    have hzero : factorWeight H j = 0 → H j = 0 := by
      intro hz
      apply norm_eq_zero.mp
      simpa [factorWeight] using hz
    by_cases hz : factorWeight H j = 0
    · have hHj : H j = 0 := hzero hz
      change factorLinearMap H hH (v j) = H j
      simp [v, factorLinearMap, factorWeight, hHj]
    · have hp : 0 < factorWeight H j := by
        rw [factorWeight]
        exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hs : Real.sqrt (factorWeight H j) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
      change factorLinearMap H hH (v j) = H j
      dsimp [factorLinearMap]
      have hcoord (k : ι) : v j k =
          if k = j then Real.sqrt (factorWeight H j) else 0 := by
        by_cases hkj : k = j
        · subst k
          simp [v, lp.coeFn_smul, lp.single_apply]
        · simp [v, lp.coeFn_smul, hkj]
      have hsingle : (fun k : ι =>
          v j k • factorNormalized H k) = fun k => if k = j then
              Real.sqrt (factorWeight H j) • factorNormalized H j else 0 := by
        funext k
        rw [hcoord k]
        by_cases hkj : k = j
        · subst k
          simp
        · simp [hkj]
      rw [hsingle, tsum_eq_single j]
      · simp only [ite_true, smul_smul, factorNormalized]
        rw [mul_inv_cancel₀ hs]
        simp
      · intro k hkj
        simp [hkj]

end ASDExplicitGamma.Gaussian
