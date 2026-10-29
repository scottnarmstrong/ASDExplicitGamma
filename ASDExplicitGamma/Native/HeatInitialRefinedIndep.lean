module

public import ASDExplicitGamma.Native.HeatInitialRefinedSplit
public import ASDExplicitGamma.Native.HeatInitialRefinedBase
public import ASDExplicitGamma.Native.HeatInitialCrossTypeTwo
public import ASDExplicitGamma.Native.HeatInitialProduct

/-! Measurability, locality and independence of the refined start components:
the old observables depend on shells up to `m + 1`, the fresh center vector
on the shells `m + 2, ..., m + 10`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3.Provider.BadEvents Algsuperdiff.Section4.Provider.Annular
open Algsuperdiff.Frozen.Assumptions
open scoped ENNReal BigOperators

noncomputable section

set_option linter.constructorNameAsVariable false

theorem nativeHeatRefinedFreshRaw_measurable (m : ℤ) :
    Measurable (nativeHeatQ3RefinedCarrierSourceFreshRaw m) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold nativeHeatQ3RefinedCarrierSourceFreshRaw
  change Measurable (fun ω => (nativeHeatQ3RefinedCarrierSourceCenterMap m
    (modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) i)
  unfold nativeHeatQ3RefinedCarrierSourceCenterMap childCenterMap
  exact (ContinuousMap.evalCLM ℝ (nativeHeatQ3RefinedCarrierCenter m i)).continuous.measurable.comp
    (measurable_modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShells m))

theorem nativeHeatRefinedFreshRaw_shellLocal (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) (nativeHeatQ3RefinedCarrierIndex → ℝ)
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val)
      inferInstance (nativeHeatQ3RefinedCarrierSourceFreshRaw m) := by
  classical
  let J : Set ℤ := Set.Icc (m + 2) (m + 10)
  let K : Set (Vec 2) := nativeHeatQ3RefinedCarrierDomain m
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    (Cutoff.shellIndexSigma J).comap Subtype.val
  have hlabel (d : Fin 9) : nativeHeatQ3RefinedCarrierPhysicalShells m d ∈ J :=
    nativeHeatQ3RefinedCarrierPhysicalShells_mem m d
  have hcoord (d : Fin 9) : @Measurable (Cutoff.CutoffSample 2) (ShellField 2)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
      (fun ω => ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)) := by
    apply measurable_iff_comap_le.mpr
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun ξ : Cutoff.ShellSeq 2 => ξ (nativeHeatQ3RefinedCarrierPhysicalShells m d))
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (hlabel d))
      (by funext ω; rfl)
  have hband : @Measurable (Cutoff.CutoffSample 2) (C(K, ℝ))
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
      (fun ω => modelBand K (nativeHeatQ3RefinedCarrierPhysicalShells m) ω) := by
    unfold Gaussian.modelBand
    apply Finset.measurable_sum
    intro d hd
    exact (measurable_shellFieldScalarRestriction K).comp (hcoord d)
  apply measurable_pi_iff.mpr
  intro i
  unfold nativeHeatQ3RefinedCarrierSourceFreshRaw
  change @Measurable (Cutoff.CutoffSample 2) ℝ
    ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
    (fun ω => (nativeHeatQ3RefinedCarrierSourceCenterMap m
      (modelBand K (nativeHeatQ3RefinedCarrierPhysicalShells m) ω)) i)
  unfold nativeHeatQ3RefinedCarrierSourceCenterMap childCenterMap
  exact (ContinuousMap.evalCLM ℝ (nativeHeatQ3RefinedCarrierCenter m i)).continuous.measurable.comp
    hband

theorem nativeHeatRefinedZ_measurable (M : ABKModel 2) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    Measurable (fun ω => nativeHeatQ3RefinedCarrierSourceZ M m ω i) := by
  unfold nativeHeatQ3RefinedCarrierSourceZ
  exact (measurable_const.mul ((measurable_pi_apply i).comp
    (nativeHeatRefinedFreshRaw_measurable m))).div_const _

theorem nativeHeatRefinedZ_shellLocal (M : ABKModel 2) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val)
      inferInstance (fun ω => nativeHeatQ3RefinedCarrierSourceZ M m ω i) := by
  unfold nativeHeatQ3RefinedCarrierSourceZ
  exact (measurable_const.mul ((measurable_pi_apply i).comp
    (nativeHeatRefinedFreshRaw_shellLocal m))).div_const _

theorem nativeHeatRefinedCenterQuadratic_measurable (M : ABKModel 2) (m : ℤ) :
    Measurable (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m) := by
  unfold nativeHeatQ3RefinedCarrierSourceCenterQuadratic
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (nativeHeatRefinedZ_measurable M m i).pow_const 2)

theorem nativeHeatRefinedCenterQuadratic_shellLocal (M : ABKModel 2) (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val)
      inferInstance (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m) := by
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    (Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val
  unfold nativeHeatQ3RefinedCarrierSourceCenterQuadratic
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (nativeHeatRefinedZ_shellLocal M m i).pow_const 2)

theorem nativeHeatRefinedOldAverage_local (M : ABKModel 2) (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M (m + 1) Set.univ) (borel ℝ)
      (nativeHeatRefinedOldAverage M m) := by
  unfold nativeHeatRefinedOldAverage
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact (Cold.coldNativeCellTrace_local M (m + 1)
    (nativeHeatQ3RefinedCarrierChild m i)).mono
    (cutoffSampleLocalSigma_mono M le_rfl (Set.subset_univ _)) le_rfl

/-- The refined old average and the fresh center quadratic are independent. -/
theorem nativeHeatRefinedOldFresh_independent (M : ABKModel 2) (m : ℤ) :
    IndepFun (nativeHeatRefinedOldAverage M m)
      (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hJ : Disjoint (Set.Iic (m + 1)) (Set.Icc (m + 2) (m + 10)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with ⟨hzLo, hzHi⟩
    change z ≤ m + 1 at hz
    omega
  exact nativeHeat_cutoffLocal_freshBlock_independent M (m + 1) _ hJ _
    (nativeHeatRefinedOldAverage_local M m) _
    (nativeHeatRefinedCenterQuadratic_shellLocal M m)


/-- The refined child shear has finite second moment. -/
theorem nativeHeatRefinedShear_memLp_two
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    MemLp (fun ω : Cutoff.CutoffSample 2 =>
      Variational.shearTraceLinear (coarseBlockMatrix
        (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have htrace := (nativeHeatRefinedCell_L20 M h hM hg m hpast i).1.mono_exponent
    (by norm_num : (2 : ℝ≥0∞) ≤ 20)
  have h01 := Cold.coldNativeResponse_memLp_of_trace M (m + 1)
    (nativeHeatQ3RefinedCarrierChild m i) htrace (Sum.inl 1) (Sum.inr 0)
  have h10 := Cold.coldNativeResponse_memLp_of_trace M (m + 1)
    (nativeHeatQ3RefinedCarrierChild m i) htrace (Sum.inl 0) (Sum.inr 1)
  have hfun : (fun ω : Cutoff.CutoffSample 2 =>
      Variational.shearTraceLinear (coarseBlockMatrix
        (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) =
      fun ω => Cold.coldNativeResponse M (m + 1)
          (nativeHeatQ3RefinedCarrierChild m i) ω (Sum.inl 1) (Sum.inr 0) -
        Cold.coldNativeResponse M (m + 1)
          (nativeHeatQ3RefinedCarrierChild m i) ω (Sum.inl 0) (Sum.inr 1) := by
    funext ω
    simp [Cold.coldNativeResponse, Variational.shearTraceLinear,
      Variational.frameMatrix, Homogenization.toFullBlockMat]
  rw [hfun]
  exact h01.sub h10

/-- The refined shear cross term is integrable with mean zero: each old child
shear is centred and independent of the fresh centers. -/
theorem nativeHeatRefinedShearCross_integrable_zero
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (hYint : Integrable (nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m)
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    Integrable (nativeHeatQ3RefinedCarrierSourceShearCross M m)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, nativeHeatQ3RefinedCarrierSourceShearCross M m ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure = 0 := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let Zf := nativeHeatQ3RefinedCarrierSourceZ M m
  let N : ℝ := (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)
  have hJ : Disjoint (Set.Iic (m + 1)) (Set.Icc (m + 2) (m + 10)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with ⟨hzLo, hzHi⟩
    change z ≤ m + 1 at hz
    omega
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hZmem (i : nativeHeatQ3RefinedCarrierIndex) : MemLp (fun ω => Zf ω i) 2 μ := by
    have hmeas := nativeHeatRefinedZ_measurable M m i
    have hle : ∀ ω, (Zf ω i) ^ 2 ≤ N * nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m ω := by
      intro ω
      unfold nativeHeatQ3RefinedCarrierSourceCenterQuadratic
      change (Zf ω i) ^ 2 ≤ N * (N⁻¹ * ∑ j, (Zf ω j) ^ 2)
      rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
      exact Finset.single_le_sum (f := fun j => (Zf ω j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hint : Integrable (fun ω => (Zf ω i) ^ 2) μ := by
      refine Integrable.mono' (hYint.const_mul N) (hmeas.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hle ω
    exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hint
  have hcell (i : nativeHeatQ3RefinedCarrierIndex) :
      Integrable (fun ω => Zf ω i * Variational.shearTraceLinear
        (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) μ ∧
      ∫ ω, Zf ω i * Variational.shearTraceLinear
        (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun) ∂μ = 0 := by
    let Ys : Cutoff.CutoffSample 2 → ℝ := fun ω => Variational.shearTraceLinear
      (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)
    have hYmem := nativeHeatRefinedShear_memLp_two M h hM hg m hpast i
    have hXlocal : @Measurable (Cutoff.CutoffSample 2) ℝ
        (Cutoff.cutoffSampleLocalSigma M (m + 1) Set.univ) (borel ℝ) Ys := by
      let shear : FullBlockMat 2 → ℝ := fun A =>
        A (Sum.inl 1) (Sum.inr 0) - A (Sum.inl 0) (Sum.inr 1)
      have hshear : Measurable shear := by fun_prop
      have hresp := (Cold.coldNativeResponse_local M (m + 1)
        (nativeHeatQ3RefinedCarrierChild m i)).mono
        (cutoffSampleLocalSigma_mono M le_rfl (Set.subset_univ _)) le_rfl
      have hEq : Ys = fun ω => shear (Cold.coldNativeResponse M (m + 1)
          (nativeHeatQ3RefinedCarrierChild m i) ω) := by
        funext ω
        simp [Ys, shear, Cold.coldNativeResponse, Variational.shearTraceLinear,
          Variational.frameMatrix, Homogenization.toFullBlockMat]
      rw [hEq]
      exact hshear.comp hresp
    have hind : IndepFun Ys (fun ω => Zf ω i) μ :=
      nativeHeat_cutoffLocal_freshBlock_independent M (m + 1) _ hJ Ys hXlocal _
        (nativeHeatRefinedZ_shellLocal M m i)
    have hcenter := nativeHeat_oldShear_centered M (m + 1)
      (nativeHeatQ3RefinedCarrierChild m i)
      ((nativeHeatRefinedCell_L20 M h hM hg m hpast i).1.mono_exponent
        (by norm_num : (2 : ℝ≥0∞) ≤ 20))
    have hmulInt : Integrable (fun ω => Ys ω * Zf ω i) μ :=
      hYmem.integrable_mul (hZmem i)
    have hmulZero : ∫ ω, Ys ω * Zf ω i ∂μ = 0 := by
      calc
        _ = (∫ ω, Ys ω ∂μ) * (∫ ω, Zf ω i ∂μ) :=
          hind.integral_mul_eq_mul_integral hYmem.aestronglyMeasurable
            (hZmem i).aestronglyMeasurable
        _ = 0 := by
          have : ∫ ω, Ys ω ∂μ = 0 := hcenter
          rw [this]; simp
    have hfun : (fun ω => Zf ω i * Variational.shearTraceLinear
        (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) =
        fun ω => Ys ω * Zf ω i := by
      funext ω; ring
    rw [hfun]
    exact ⟨hmulInt, hmulZero⟩
  have hsumInt : Integrable (fun ω => ∑ i, Zf ω i * Variational.shearTraceLinear
      (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) μ :=
    integrable_finset_sum _ fun i _ => (hcell i).1
  have hfun : nativeHeatQ3RefinedCarrierSourceShearCross M m = fun ω =>
      (2 * N⁻¹) * ∑ i, Zf ω i * Variational.shearTraceLinear
        (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
          (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun) := by
    funext ω
    unfold nativeHeatQ3RefinedCarrierSourceShearCross
    ring
  rw [hfun]
  refine ⟨hsumInt.const_mul _, ?_⟩
  rw [integral_const_mul, integral_finset_sum _ fun i _ => (hcell i).1]
  simp [fun i => (hcell i).2]

end

end ASDExplicitGamma.Native
