/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.RealizationMeasurability
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Gaussian laws of Hilbert-factorized series

This file identifies the finite-dimensional laws of the selected a.e. limit of a
Hilbert-valued Gaussian series.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

universe u

private theorem map_finiteGaussianLinearCombination {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
        (fun x : ι → ℝ => ∑ i, x i * a i) =
      gaussianReal 0 (Real.toNNReal (∑ i, a i ^ 2)) := by
  let E := EuclideanSpace ℝ ι
  let c : E := WithLp.toLp 2 a
  let L : StrongDual ℝ E := innerSL ℝ c
  have hfun : (fun x : ι → ℝ => ∑ i, x i * a i) =
      fun x => L (WithLp.toLp 2 x) := by
    funext x
    change (∑ i, x i * a i) = ⟪WithLp.toLp 2 a, WithLp.toLp 2 x⟫
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hnorm : ‖L‖ ^ 2 = ∑ i, a i ^ 2 := by
    change ‖innerSL ℝ c‖ ^ 2 = _
    rw [innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
  have hpi := ProbabilityTheory.map_pi_eq_stdGaussian (ι := ι)
  calc
    _ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map
        (fun x => L (WithLp.toLp 2 x)) := by rw [hfun]
    _ = ((Measure.pi (fun _ : ι => gaussianReal 0 1)).map (WithLp.toLp 2)).map L := by
      simpa only [Function.comp_def] using
        (Measure.map_map (g := L) (f := WithLp.toLp 2)
          (by fun_prop) (by fun_prop)).symm
    _ = (stdGaussian E).map L := by rw [hpi]
    _ = gaussianReal 0 (Real.toNNReal (∑ i, a i ^ 2)) := by
      rw [ProbabilityTheory.IsGaussian.map_eq_gaussianReal L,
        ProbabilityTheory.integral_strongDual_stdGaussian,
        ProbabilityTheory.variance_dual_stdGaussian, hnorm]

/-- The first `n` terms of the scalar Gaussian series with coefficients `a`. -/
def gaussianScalarPartialSum (a : ℕ → ℝ) (n : ℕ)
    (ω : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ω j * a j

private theorem gaussianScalarPartialSum_eq_apply {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (T : V →L[ℝ] E) (L : E →L[ℝ] ℝ) (n : ℕ) (ω : ℕ → ℝ) :
    gaussianScalarPartialSum (fun j => (L.comp T) (v j)) n ω =
      L (T (gaussianPartialSum v n ω)) := by
  simp [gaussianScalarPartialSum, gaussianPartialSum, map_sum, map_smul]

private def continuousMapEvalVector {K : Type u} [TopologicalSpace K]
    (ι : Type u) [Fintype ι]
    (x : ι → K) (f : C(K, ℝ)) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => f (x i))

/-- A finite linear combination of evaluations on `C(K, ℝ)`. -/
def continuousMapEvalLinearCombination {K : Type u} [TopologicalSpace K]
    (ι : Type u) [Fintype ι]
    (x : ι → K) (t : ι → ℝ) (f : C(K, ℝ)) : ℝ :=
  ∑ i, t i * f (x i)

private theorem continuousMapEvalVector_map_eq {K : Type u} [TopologicalSpace K]
    (μ ν : Measure C(K, ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hcomb : ∀ {ι : Type u} [Fintype ι] (x : ι → K) (t : ι → ℝ),
      μ.map (continuousMapEvalLinearCombination ι x t) =
        ν.map (continuousMapEvalLinearCombination ι x t))
    (ι : Type u) [Fintype ι] (x : ι → K) :
    μ.map (continuousMapEvalVector ι x) = ν.map (continuousMapEvalVector ι x) := by
  apply Measure.ext_of_charFun
  funext t
  have hinner (f : C(K, ℝ)) :
      ⟪continuousMapEvalVector ι x f, t⟫ = continuousMapEvalLinearCombination ι x t f := by
    change ⟪WithLp.toLp 2 (fun i => f (x i)), WithLp.toLp 2 t⟫ = _
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [continuousMapEvalLinearCombination, dotProduct]
  have hY : Measurable (continuousMapEvalVector ι x) := by
    change Measurable (fun f : C(K, ℝ) => WithLp.toLp 2 (fun i : ι => f (x i)))
    exact (WithLp.measurable_toLp 2 (ι → ℝ)).comp
      (measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval (x i))
  rw [charFun_map_eq_charFun_map_inner_one
    (Y := continuousMapEvalVector ι x) hY.aemeasurable t,
    charFun_map_eq_charFun_map_inner_one
    (μ := ν) (Y := continuousMapEvalVector ι x) hY.aemeasurable t]
  have hμ : μ.map (fun f => ⟪continuousMapEvalVector ι x f, t⟫) =
      μ.map (continuousMapEvalLinearCombination ι x t) :=
    congrArg (fun g : C(K, ℝ) → ℝ => μ.map g) (funext hinner)
  have hν : ν.map (fun f => ⟪continuousMapEvalVector ι x f, t⟫) =
      ν.map (continuousMapEvalLinearCombination ι x t) :=
    congrArg (fun g : C(K, ℝ) → ℝ => ν.map g) (funext hinner)
  rw [hμ, hν]
  exact congrArg (fun m : Measure ℝ => charFun m 1) (hcomb (ι := ι) x t.ofLp)

private abbrev ContinuousMapEvalConstraint (K : Type u) :=
  K × {s : Set ℝ // MeasurableSet s}

private def continuousMapFiniteEvalCylinder {K : Type u} [TopologicalSpace K]
    (I : Finset (ContinuousMapEvalConstraint K)) : Set C(K, ℝ) :=
  ⋂ p ∈ I, {f | f p.1 ∈ p.2.1}

private def continuousMapFiniteEvalCylinderBase {K : Type u} (I : Finset
    (ContinuousMapEvalConstraint K)) : Set (EuclideanSpace ℝ I) :=
  {z | ∀ p : I, z p ∈ p.1.2.1}

private theorem isPiSystem_continuousMapFiniteEvalCylinder {K : Type u} [TopologicalSpace K] :
    IsPiSystem (Set.range (continuousMapFiniteEvalCylinder (K := K))) := by
  classical
  intro s hs t ht hne
  rcases hs with ⟨I, rfl⟩
  rcases ht with ⟨J, rfl⟩
  refine ⟨I ∪ J, ?_⟩
  ext f
  simp only [continuousMapFiniteEvalCylinder, Set.mem_iInter, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro p hp
      exact h p (Finset.mem_union.mpr (Or.inl hp))
    · intro p hp
      exact h p (Finset.mem_union.mpr (Or.inr hp))
  · rintro ⟨hI, hJ⟩ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hI p hp
    · exact hJ p hp

private theorem borel_eq_generate_continuousMapFiniteEvalCylinder {K : Type u}
    [TopologicalSpace K] [SecondCountableTopology K] [LocallyCompactSpace K] :
    borel C(K, ℝ) =
      MeasurableSpace.generateFrom (Set.range (continuousMapFiniteEvalCylinder (K := K))) := by
  classical
  apply le_antisymm
  · rw [ContinuousMap.borel_eq_iSup_comap_eval]
    refine iSup_le fun x => ?_
    intro s hs
    rcases hs with ⟨s, hs, rfl⟩
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{(x, ⟨s, hs⟩)}, ?_⟩
    ext f
    simp [continuousMapFiniteEvalCylinder]
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨I, rfl⟩
    unfold continuousMapFiniteEvalCylinder
    exact I.measurableSet_biInter fun p hp =>
      measurableSet_preimage (ContinuousMap.measurable_eval p.1) p.2.2

/-- Finite evaluation linear-combination laws determine a probability measure on a continuous-map
space. The compact-open Borel structure is generated by finite cylinders in the evaluations. -/
theorem measure_eq_of_continuousMap_eval_linearCombination
    {K : Type u} [TopologicalSpace K] [SecondCountableTopology K]
    [LocallyCompactSpace K] (μ ν : Measure C(K, ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hcomb : ∀ {ι : Type u} [Fintype ι] (x : ι → K) (t : ι → ℝ),
      μ.map (continuousMapEvalLinearCombination ι x t) =
        ν.map (continuousMapEvalLinearCombination ι x t)) :
    μ = ν := by
  classical
  apply MeasureTheory.ext_of_generate_finite (m0 := borel C(K, ℝ))
    (Set.range (continuousMapFiniteEvalCylinder (K := K)))
    (borel_eq_generate_continuousMapFiniteEvalCylinder (K := K))
    isPiSystem_continuousMapFiniteEvalCylinder
  · intro s hs
    obtain ⟨I, rfl⟩ := hs
    let x : I → K := fun p => p.1.1
    have hvec := continuousMapEvalVector_map_eq μ ν hcomb I x
    let e : C(K, ℝ) → EuclideanSpace ℝ I := continuousMapEvalVector I x
    have hbase : MeasurableSet (continuousMapFiniteEvalCylinderBase I) := by
      have hset : continuousMapFiniteEvalCylinderBase I =
          ⋂ p : I, {z : EuclideanSpace ℝ I | z p ∈ p.1.2.1} := by
        ext z
        simp [continuousMapFiniteEvalCylinderBase]
      rw [hset]
      refine MeasurableSet.iInter fun p => ?_
      have hcoord : Measurable (fun z : EuclideanSpace ℝ I => z p) := by
        exact (measurable_pi_apply p).comp (WithLp.measurable_ofLp 2 (I → ℝ))
      exact measurableSet_preimage hcoord p.1.2.2
    have hpre : e ⁻¹' continuousMapFiniteEvalCylinderBase I =
        continuousMapFiniteEvalCylinder I := by
      ext f
      simp [e, x, continuousMapEvalVector, continuousMapFiniteEvalCylinderBase,
        continuousMapFiniteEvalCylinder]
    have he : Measurable e := by
      change Measurable (fun f : C(K, ℝ) => WithLp.toLp 2 (fun p : I => f (x p)))
      exact (WithLp.measurable_toLp 2 (I → ℝ)).comp
        (measurable_pi_iff.mpr fun p => ContinuousMap.measurable_eval (x p))
    calc
      μ (continuousMapFiniteEvalCylinder I) = μ (e ⁻¹' continuousMapFiniteEvalCylinderBase I) :=
        congrArg μ hpre.symm
      _ = (μ.map e) (continuousMapFiniteEvalCylinderBase I) :=
        (Measure.map_apply he hbase).symm
      _ = (ν.map e) (continuousMapFiniteEvalCylinderBase I) :=
        congrArg (fun m : Measure (EuclideanSpace ℝ I) => m _) hvec
      _ = ν (e ⁻¹' continuousMapFiniteEvalCylinderBase I) :=
        Measure.map_apply he hbase
      _ = ν (continuousMapFiniteEvalCylinder I) := congrArg ν hpre
  · simp

private def continuousMapEvalLinearCombinationCLM {K : Type u} [TopologicalSpace K]
    (ι : Type u) [Fintype ι] (x : ι → K) (t : ι → ℝ) :
    C(K, ℝ) →L[ℝ] ℝ :=
  ∑ i, t i • ContinuousMap.evalCLM ℝ (x i)

private theorem continuousMapEvalLinearCombinationCLM_apply {K : Type u}
    [TopologicalSpace K] (ι : Type u) [Fintype ι] (x : ι → K) (t : ι → ℝ)
    (f : C(K, ℝ)) :
    continuousMapEvalLinearCombinationCLM ι x t f =
      continuousMapEvalLinearCombination ι x t f := by
  simp [continuousMapEvalLinearCombinationCLM, continuousMapEvalLinearCombination,
    ContinuousMap.evalCLM_apply]

private theorem gaussianSeriesEvalVariance_eq_kernelSum {K : Type u}
    [TopologicalSpace K] [CompactSpace K] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] (v : ℕ → V)
    (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] C(K, ℝ))
    (ι : Type u) [Fintype ι] (x : ι → K) (t : ι → ℝ) (C : K → K → ℝ)
    (hKernel : ∀ x y, (∑' j, T (v j) x * T (v j) y) = C x y) :
    (∑' j, (continuousMapEvalLinearCombinationCLM ι x t (T (v j))) ^ 2) =
      ∑ i, ∑ k, t i * t k * C (x i) (x k) := by
  let L := continuousMapEvalLinearCombinationCLM ι x t
  let F : ι × ι → ℕ → ℝ := fun p j =>
    (t p.1 * t p.2) * (T (v j) (x p.1) * T (v j) (x p.2))
  have hdir := summable_sq_norm_gaussianDirections hA T
  have hpair (x y : K) : Summable (fun j => T (v j) x * T (v j) y) := by
    apply Summable.of_abs
    apply hdir.of_nonneg_of_le (fun j => abs_nonneg _)
    intro j
    calc
      |T (v j) x * T (v j) y| = ‖T (v j) x * T (v j) y‖ := by
        rw [Real.norm_eq_abs]
      _ = ‖T (v j) x‖ * ‖T (v j) y‖ := norm_mul _ _
      _ ≤ ‖T (v j)‖ * ‖T (v j)‖ := by
        exact mul_le_mul (ContinuousMap.norm_coe_le_norm (T (v j)) x)
          (ContinuousMap.norm_coe_le_norm (T (v j)) y) (norm_nonneg _) (norm_nonneg _)
      _ = ‖T (v j)‖ ^ 2 := by ring
  have hterm (p : ι × ι) : Summable (fun j => |F p j|) := by
    have hp := (hpair (x p.1) (x p.2)).abs
    have hscaled := hp.mul_left |t p.1 * t p.2|
    apply hscaled.congr
    intro j
    simp [F, abs_mul]
  have hprodNorm : Summable (fun q : (ι × ι) × ℕ => |F q.1 q.2|) := by
    rw [summable_prod_of_nonneg (fun q => abs_nonneg (F q.1 q.2))]
    exact ⟨hterm, Summable.of_finite⟩
  have hprod : Summable (Function.uncurry F) := by
    exact Summable.of_abs (by simpa [Function.uncurry] using hprodNorm)
  have hL (j : ℕ) : L (T (v j)) = ∑ i, t i * T (v j) (x i) := by
    simp [L, continuousMapEvalLinearCombinationCLM, ContinuousMap.evalCLM_apply]
  have hsquare (j : ℕ) :
      (L (T (v j))) ^ 2 = ∑ p : ι × ι, F p j := by
    rw [hL]
    calc
      (∑ i, t i * T (v j) (x i)) ^ 2 =
          ∑ i, ∑ k, (t i * T (v j) (x i)) * (t k * T (v j) (x k)) := by
        rw [pow_two, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = ∑ p : ι × ι, F p j := by
        symm
        simpa [F, mul_assoc, mul_left_comm, mul_comm] using
          (Fintype.sum_prod_type (fun p : ι × ι =>
            (t p.1 * T (v j) (x p.1)) * (t p.2 * T (v j) (x p.2))) :
            ∑ p : ι × ι,
                (t p.1 * T (v j) (x p.1)) * (t p.2 * T (v j) (x p.2)) = _)
  calc
    _ = ∑' j, ∑ p : ι × ι, F p j := by
      congr 1
      funext j
      exact hsquare j
    _ = ∑' j, ∑' p : ι × ι, F p j := by simp
    _ = ∑' p : ι × ι, ∑' j, F p j := Summable.tsum_comm hprod
    _ = ∑ p : ι × ι, ∑' j, F p j := by simp
    _ = ∑ i, ∑ k, t i * t k * C (x i) (x k) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rw [(hpair (x i) (x k)).tsum_mul_left,
        hKernel (x i) (x k)]

/-- Every finite scalar projection of the product Gaussian series has its expected Gaussian law.
The variance is the sum of the squared coefficients used by that partial sum. -/
theorem map_gaussianScalarPartialSum (a : ℕ → ℝ) (n : ℕ) :
    standardGaussianInfinitePi.map (gaussianScalarPartialSum a n) =
      gaussianReal 0 (Real.toNNReal (∑ j ∈ Finset.range n, a j ^ 2)) := by
  let I : Finset ℕ := Finset.range n
  let b : I → ℝ := fun i => a i
  let g : (I → ℝ) → ℝ := fun z => ∑ i, z i * b i
  have hrestrict : standardGaussianInfinitePi.map I.restrict =
      Measure.pi (fun _ : I => gaussianReal 0 1) := by
    change (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)).map I.restrict = _
    exact Measure.infinitePi_map_restrict
      (μ := fun _ : ℕ => gaussianReal 0 1) (I := I)
  have hg : Measurable g := by fun_prop
  have hfun (ω : ℕ → ℝ) : gaussianScalarPartialSum a n ω = g (I.restrict ω) := by
    change (∑ j ∈ I, ω j * a j) = ∑ i ∈ I.attach, ω i.1 * a i.1
    exact (Finset.sum_attach I (fun j => ω j * a j)).symm
  have hvariance : (∑ i : I, b i ^ 2) = ∑ j ∈ I, a j ^ 2 := by
    change (∑ i ∈ I.attach, a i.1 ^ 2) = ∑ j ∈ I, a j ^ 2
    exact Finset.sum_attach I (fun j => a j ^ 2)
  calc
    _ = standardGaussianInfinitePi.map (g ∘ I.restrict) := by
      congr 1
      funext ω
      exact hfun ω
    _ = (standardGaussianInfinitePi.map I.restrict).map g := by
      simpa only [Function.comp_def] using
        (Measure.map_map (μ := standardGaussianInfinitePi) (g := g) (f := I.restrict)
          hg (Finset.measurable_restrict I)).symm
    _ = (Measure.pi (fun _ : I => gaussianReal 0 1)).map g := by rw [hrestrict]
    _ = gaussianReal 0 (Real.toNNReal (∑ i : I, b i ^ 2)) := by
      simpa only [g, b] using map_finiteGaussianLinearCombination b
    _ = gaussianReal 0 (Real.toNNReal (∑ j ∈ Finset.range n, a j ^ 2)) := by
      congr 1
      rw [hvariance]

/-- A scalar continuous linear projection of the selected Gaussian series limit is centered
Gaussian. Its variance is the sum of the squared projected directions. -/
theorem map_gaussianSeriesLimitE_linear {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [OpensMeasurableSpace E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] E) (L : E →L[ℝ] ℝ) :
    standardGaussianInfinitePi.map (fun ω => L (gaussianSeriesLimitE hA T ω)) =
      gaussianReal 0 (Real.toNNReal (∑' j, (L (T (v j))) ^ 2)) := by
  let a : ℕ → ℝ := fun j => (L.comp T) (v j)
  let X : ℕ → (ℕ → ℝ) → ℝ := fun k ω =>
    gaussianScalarPartialSum a (gaussianFastIndex hA k) ω
  let Z : (ℕ → ℝ) → ℝ := fun ω => L (gaussianSeriesLimitE hA T ω)
  have hcoeff : Summable (fun j => a j ^ 2) := by
    have h := summable_sq_norm_gaussianDirections hA (L.comp T)
    simpa [a, Real.norm_eq_abs, sq_abs] using h
  have hindex : Tendsto (gaussianFastIndex hA) atTop atTop :=
    (gaussianFastIndex_strictMono hA).tendsto_atTop
  have hvariance : Tendsto
      (fun k => ∑ j ∈ Finset.range (gaussianFastIndex hA k), a j ^ 2)
      atTop (𝓝 (∑' j, a j ^ 2)) :=
    hcoeff.tendsto_sum_tsum_nat.comp hindex
  have hvarianceNN : Tendsto
      (fun k => Real.toNNReal
        (∑ j ∈ Finset.range (gaussianFastIndex hA k), a j ^ 2))
      atTop (𝓝 (Real.toNNReal (∑' j, a j ^ 2))) :=
    tendsto_real_toNNReal hvariance
  have hpartialMap (k : ℕ) : standardGaussianInfinitePi.map (X k) =
      gaussianReal 0 (Real.toNNReal
        (∑ j ∈ Finset.range (gaussianFastIndex hA k), a j ^ 2)) := by
    simpa [X] using map_gaussianScalarPartialSum a (gaussianFastIndex hA k)
  have hchar (t : ℝ) : Tendsto
      (fun k => charFun
        (standardGaussianInfinitePi.map (X k)) t)
      atTop (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (∑' j, a j ^ 2))) t)) := by
    let f : NNReal → ℂ := fun s => Complex.exp
      (-(s : ℂ) * (t : ℂ) ^ 2 / 2)
    have hf : Continuous f := by fun_prop
    have hexp : Tendsto
        (fun k => f (Real.toNNReal
          (∑ j ∈ Finset.range (gaussianFastIndex hA k), a j ^ 2)))
        atTop (𝓝 (f (Real.toNNReal (∑' j, a j ^ 2)))) :=
      hf.continuousAt.tendsto.comp hvarianceNN
    have hsource (k : ℕ) : charFun (standardGaussianInfinitePi.map (X k)) t =
        f (Real.toNNReal
          (∑ j ∈ Finset.range (gaussianFastIndex hA k), a j ^ 2)) := by
      rw [hpartialMap k, charFun_gaussianReal]
      simp only [f]
      apply congrArg Complex.exp
      norm_num
      ring_nf
    have htarget : charFun (gaussianReal 0
        (Real.toNNReal (∑' j, a j ^ 2))) t = f (Real.toNNReal (∑' j, a j ^ 2)) := by
      rw [charFun_gaussianReal]
      simp only [f]
      apply congrArg Complex.exp
      norm_num
      ring_nf
    simpa only [hsource, htarget] using hexp
  have hXmeas (k : ℕ) : AEMeasurable (X k) standardGaussianInfinitePi := by
    dsimp [X, a, gaussianScalarPartialSum]
    exact (by fun_prop : Measurable
      (fun ω : ℕ → ℝ => ∑ j ∈ Finset.range (gaussianFastIndex hA k),
        ω j * (L (T (v j))))).aemeasurable
  have hZmeas : AEMeasurable Z standardGaussianInfinitePi := by
    dsimp [Z]
    exact (L.continuous.comp_stronglyMeasurable
      (stronglyMeasurable_gaussianSeriesLimitE hA T)).aemeasurable
  have hGaussian : MeasureTheory.TendstoInDistribution X atTop
      (fun x : ℝ => x) (fun _ : ℕ => standardGaussianInfinitePi)
      (gaussianReal 0 (Real.toNNReal (∑' j, a j ^ 2))) := by
    refine MeasureTheory.TendstoInDistribution.of_tendsto_charFun
      (P := fun _ : ℕ => standardGaussianInfinitePi)
      (P' := gaussianReal 0 (Real.toNNReal (∑' j, a j ^ 2)))
      (X' := fun x : ℝ => x) hXmeas (by fun_prop) ?_
    intro t
    simpa [Measure.map_id] using hchar t
  have hlimit : ∀ᵐ ω ∂standardGaussianInfinitePi,
      Tendsto (fun k => X k ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [ae_tendsto_gaussianSeriesLimitE hA T] with ω hω
    have hω' := L.continuous.continuousAt.tendsto.comp hω
    have hseq (k : ℕ) : X k ω =
        L (T (gaussianFastPartialSumSequence hA k ω)) := by
      simpa [X, a, gaussianFastPartialSumSequence] using
        (gaussianScalarPartialSum_eq_apply T L
          (gaussianFastIndex hA k) ω)
    simpa [Z, Function.comp_def, hseq] using hω'
  have hLimitDistribution : MeasureTheory.TendstoInDistribution X atTop Z
      (fun _ : ℕ => standardGaussianInfinitePi) standardGaussianInfinitePi :=
    MeasureTheory.tendstoInDistribution_of_ae_tendsto hXmeas hZmeas hlimit
  have heq := MeasureTheory.tendstoInDistribution_unique X hGaussian hLimitDistribution
  simpa [Z, a, Measure.map_id] using heq.symm

/-- The scalar shell restriction and a Hilbert-factorized Gaussian series have the same law on a
compact set whenever their finite evaluation combinations share the given covariance kernel. -/
theorem shellFieldScalarRestriction_law_eq_gaussianSeries
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] {K : Set (Homogenization.Vec 2)}
    [CompactSpace (↥K)] [SecondCountableTopology (↥K)] [LocallyCompactSpace (↥K)]
    (μ : Measure (Algsuperdiff.Frozen.Assumptions.ShellField 2))
    [IsProbabilityMeasure μ] (C : ↥K → ↥K → ℝ)
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2))
    (T : V →L[ℝ] C(↥K, ℝ))
    (hShell : ∀ {ι : Type} [Fintype ι] (x : ι → ↥K) (t : ι → ℝ),
      μ.map (fun j => ∑ i, t i * j (x i) 1 0) =
        gaussianReal 0 (Real.toNNReal (∑ i, ∑ k, t i * t k * C (x i) (x k))))
    (hKernel : ∀ x y, (∑' j, T (v j) x * T (v j) y) = C x y) :
    μ.map (shellFieldScalarRestriction K) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
  have hRestrictMeas : Measurable (shellFieldScalarRestriction K) :=
    measurable_shellFieldScalarRestriction K
  have hSeriesMeas : Measurable (gaussianSeriesLimitE hA T) :=
    (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hcomboMeas {ι : Type} [Fintype ι] (x : ι → ↥K) (t : ι → ℝ) :
      Measurable (continuousMapEvalLinearCombination ι x t) := by
    change Measurable (fun f : C(↥K, ℝ) => ∑ i, t i * f (x i))
    exact Finset.measurable_sum Finset.univ fun i hi =>
      measurable_const.mul (ContinuousMap.measurable_eval (x i))
  have hcomb {ι : Type} [Fintype ι] (x : ι → ↥K) (t : ι → ℝ) :
      (μ.map (shellFieldScalarRestriction K)).map
          (continuousMapEvalLinearCombination ι x t) =
        (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)).map
          (continuousMapEvalLinearCombination ι x t) := by
    have hShellCombo :
        (μ.map (shellFieldScalarRestriction K)).map
            (continuousMapEvalLinearCombination ι x t) =
          μ.map (fun j => ∑ i, t i * j (x i) 1 0) := by
      rw [Measure.map_map (hcomboMeas x t) hRestrictMeas]
      rfl
    let L : C(↥K, ℝ) →L[ℝ] ℝ := continuousMapEvalLinearCombinationCLM ι x t
    have hSeriesCombo :
        (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)).map
            (continuousMapEvalLinearCombination ι x t) =
          gaussianReal 0 (Real.toNNReal (∑ i, ∑ k, t i * t k * C (x i) (x k))) := by
      have hVar := gaussianSeriesEvalVariance_eq_kernelSum v hA T ι x t C hKernel
      have hLinear := map_gaussianSeriesLimitE_linear hA T L
      calc
        (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)).map
            (continuousMapEvalLinearCombination ι x t) =
            standardGaussianInfinitePi.map
              (fun ω => continuousMapEvalLinearCombination ι x t
                (gaussianSeriesLimitE hA T ω)) :=
          Measure.map_map (hcomboMeas x t) hSeriesMeas
        _ = standardGaussianInfinitePi.map
            (fun ω => L (gaussianSeriesLimitE hA T ω)) := by
              congr 1
              funext ω
              exact (continuousMapEvalLinearCombinationCLM_apply ι x t
                (gaussianSeriesLimitE hA T ω)).symm
        _ = gaussianReal 0
            (Real.toNNReal (∑ i, ∑ k, t i * t k * C (x i) (x k))) := by
              rw [← hVar]
              exact hLinear
    rw [hShellCombo, hShell x t, hSeriesCombo]
  exact measure_eq_of_continuousMap_eval_linearCombination
    (μ.map (shellFieldScalarRestriction K))
    (standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T)) hcomb

end ASDExplicitGamma.Gaussian
