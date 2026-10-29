module

public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceStart
public import ASDExplicitGamma.Native.HeatVHEATRefinedVectorD4
public import ASDExplicitGamma.Native.HeatInitialRefinedProfile
public import ASDExplicitGamma.Native.HeatVHEATChild

/-! The exact refined start observable: pointwise decomposition of the
source-normalized depth-ten carrier into the old average, the center
quadratic, the shear cross and the rare quadratic. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Response
open scoped ENNReal BigOperators

noncomputable section

local instance nativeHeatRefinedSplitChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- The restriction of the completed older field to a child is, as a bounded
continuous function, the old response coefficient of that child. -/
theorem nativeHeatRefined_oldMap_older_eq
    (M : ABKModel 2) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ω : Cutoff.CutoffSample 2) :
    ContinuousMap.linearIsometryBoundedOfCompact
        (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) ℝ ℝ
      (nativeHeatQ3RefinedCarrierOldMap m
        (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω) i) =
      nativeHeatOldResponseCoefficient
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω := by
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (nativeHeatQ3RefinedCarrierDomain m)
    (isCompact_iff_compactSpace.mpr inferInstance)
  ext x
  have hx : x.1 ∈ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m i x.2
  have h1 := olderField_apply_eq_coefficientCutoff
    (nativeHeatQ3RefinedCarrierDomain m) M ell (m + 1) hK ω ⟨x.1, hx⟩
  change olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω ⟨x.1, hx⟩ =
    (Cutoff.cutoff (m + 1) ω) x.1 1 0
  rw [h1, ← Scalar.old_cutoff_coefficient_planar]
  simp [responsePlanarCoefficient, responsePlanarJ]
  done


/-- The actual child response at the refined cutoff, constantly shifted by `g`,
splits into the old trace, the shear cross and the frame quadratic. -/
theorem nativeHeatRefined_childTrace_shift_eq
    (M : ABKModel 2) (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex)
    (ω : Cutoff.CutoffSample 2) (g : ℝ) :
    childTraceObservable
        (measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
        (volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
        M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M (m + 1)).1
        (nativeHeatQ3RefinedCarrierOldMap m
            (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω) i +
          BoundedContinuousFunction.const
            (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) g) =
      Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i) ω +
        2 * ((g / (Annealed.sigmaBar M (m + 1) : ℝ)) *
          Variational.shearTraceLinear
            (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
        (g / (Annealed.sigmaBar M (m + 1) : ℝ)) ^ 2 *
          Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
            (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let σ : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
  let k := nativeHeatQ3RefinedCarrierOldMap m
    (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω) i
  have hrows := nativeHeat_childTrace_shear_rows
    (measurableSet_cubeSet Q) (volume_cubeSet_toReal_pos Q) M.nu σ M.nu_pos hσ k
  have hL := nativeHeatRefined_oldMap_older_eq M m i ω
  have hmat := nativeHeat_oldResponseCoarse_eq_cutoff M Q (m + 1) ω
  have hg := hrows.2.2.2 g
  have hL' : (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet Q)) ℝ ℝ) k =
      nativeHeatOldResponseCoefficient Q (m + 1) ω := hL
  simp only [hL', hmat] at hg
  rw [hg]
  have htrace : Cold.coldNativeCellTrace M (m + 1) Q ω =
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun σ := rfl
  have hT : traceDefect (cubeSet Q)
      (responsePlanarCoefficientField M.nu
        (nativeHeatOldResponseCoefficient Q (m + 1) ω)) σ =
      Cold.coldNativeCellTrace M (m + 1) Q ω := by
    rw [htrace]
    unfold traceDefect
    rw [hmat]
  rw [hT]
  rw [show (Annealed.sigmaBar M (m + 1) : ℝ) = σ from rfl]
  field_simp
  ring


local instance nativeHeatRefinedSplitNeZero : NeZero (3 ^ 10 * 3 ^ 10) :=
  ⟨by norm_num⟩

local instance nativeHeatRefinedSplitFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The old average of the refined children at the cutoff `m + 1`. -/
noncomputable def nativeHeatRefinedOldAverage
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i) ω

/-- The refined start observable: the averaged child trace of the old field
shifted by the source-normalized fresh centers. -/
noncomputable def nativeHeatRefinedObservable
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  childMeanTrace
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
    (nativeHeatQ3RefinedCarrierOldMap m
        (olderField (nativeHeatQ3RefinedCarrierDomain m) (m + 1) ω) +
      childConstantMap
        (fun i : nativeHeatQ3RefinedCarrierIndex =>
          closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)))
        (fun i => Real.sqrt (1 + (nativeHeatTheta : ℝ)) *
          nativeHeatQ3RefinedCarrierSourceFreshRaw m ω i))

theorem nativeHeatRefinedObservable_nonneg
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatRefinedObservable M m ω :=
  nativeHeat_childMeanTrace_nonneg
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      nativeHeatQ3RefinedCarrierChild m i) M.nu _ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 _

/-- Exact finite-sum form of the refined start observable. -/
theorem nativeHeatRefinedObservable_eq
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    nativeHeatRefinedObservable M m ω =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (Cold.coldNativeCellTrace M (m + 1)
              (nativeHeatQ3RefinedCarrierChild m i) ω +
            2 * (nativeHeatQ3RefinedCarrierSourceZ M m ω i *
              Variational.shearTraceLinear
                (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
                  (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
            nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2 *
              Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
                (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
                  (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight) := by
  unfold nativeHeatRefinedObservable
  rw [nativeHeat_childMeanTrace_constantShift_sum
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      nativeHeatQ3RefinedCarrierChild m i) M.nu _ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1]
  rw [Fintype.card_fin]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [nativeHeatRefined_childTrace_shift_eq]
  unfold nativeHeatQ3RefinedCarrierSourceZ
  ring


/-- Pointwise, almost surely, the refined start observable is bounded by the
old average, the center quadratic, the shear cross and the rare quadratic. -/
theorem nativeHeatRefinedObservable_le_components
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      nativeHeatRefinedObservable M m ω ≤
        nativeHeatRefinedOldAverage M m ω +
          2 * (nativeHeatB : ℝ) *
            nativeHeatQ3RefinedCarrierSourceCenterQuadratic M m ω +
          nativeHeatQ3RefinedCarrierSourceShearCross M m ω +
          nativeHeatQ3RefinedCarrierSourceRareQuadraticD4 M m ω := by
  have hprofile : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ i : nativeHeatQ3RefinedCarrierIndex,
        Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
          (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight ≤
          2 * ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderD4 M
              (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω) := by
    rw [ae_all_iff]
    intro i
    exact (nativeHeatOldInverseTraceProfileD4_of_states M h hM hg
      (nativeHeatQ3RefinedCarrierChild m i) (m + 1)
      (by have := nativeHeatQ3RefinedCarrierChild_scale m i; omega) hpast).2.2.1
  have hbase : (inverseBankCap .localInverse : ℝ) ≤ (nativeHeatB : ℝ) := by
    exact_mod_cast nativeHeat_localInverseCap_le_nativeHeatB
  filter_upwards [hprofile] with ω hω
  rw [nativeHeatRefinedObservable_eq]
  unfold nativeHeatRefinedOldAverage nativeHeatQ3RefinedCarrierSourceCenterQuadratic
    nativeHeatQ3RefinedCarrierSourceShearCross
    nativeHeatQ3RefinedCarrierSourceRareQuadraticD4
  set N : ℝ := (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hpt : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2 *
        Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
          (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight ≤
      2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2 +
        2 * nativeHeatOldInverseRemainderD4 M
          (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2 := by
    intro i
    have hsq := sq_nonneg (nativeHeatQ3RefinedCarrierSourceZ M m ω i)
    have h1 := mul_le_mul_of_nonneg_left (hω i) hsq
    have h2 : 2 * ((inverseBankCap .localInverse : ℝ) +
        nativeHeatOldInverseRemainderD4 M
          (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω) ≤
        2 * ((nativeHeatB : ℝ) + nativeHeatOldInverseRemainderD4 M
          (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hsq
    nlinarith [h1, h3]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  have key : N * ∑ i : nativeHeatQ3RefinedCarrierIndex,
      (Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i) ω +
        2 * (nativeHeatQ3RefinedCarrierSourceZ M m ω i *
          Variational.shearTraceLinear
            (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
        nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2 *
          Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
            (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight) ≤
      N * ∑ i : nativeHeatQ3RefinedCarrierIndex,
        (Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i) ω +
          2 * (nativeHeatQ3RefinedCarrierSourceZ M m ω i *
            Variational.shearTraceLinear
              (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
                (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
          (2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2 +
            2 * nativeHeatOldInverseRemainderD4 M
              (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
              nativeHeatQ3RefinedCarrierSourceZ M m ω i ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hN0
    exact Finset.sum_le_sum (fun i _ => by linarith [hpt i])
  refine key.trans (le_of_eq ?_)
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

end

end ASDExplicitGamma.Native
