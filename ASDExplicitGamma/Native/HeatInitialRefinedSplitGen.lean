module

public import ASDExplicitGamma.Native.HeatInitialRefinedSplit
public import ASDExplicitGamma.Native.HeatInitialRefinedVectorGen

/-! The exact refined start observable for `ns` shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Response
open scoped ENNReal BigOperators


noncomputable section

local instance nativeHeatRefinedSplitChildCompactGen (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatRefinedSplitNeZeroGen : NeZero (3 ^ 10 * 3 ^ 10) :=
  ⟨by norm_num⟩

local instance nativeHeatRefinedSplitFiniteGen (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The refined start observable: the averaged child trace of the old field
shifted by the source-normalized fresh centers. -/
noncomputable def nativeHeatRefinedObservableGen (ns : ℕ)
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
          nativeHeatQ3RefinedCarrierSourceFreshRawGen ns m ω i))

theorem nativeHeatRefinedObservable_nonneg_Gen (ns : ℕ)
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ nativeHeatRefinedObservableGen ns M m ω :=
  nativeHeat_childMeanTrace_nonneg
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      nativeHeatQ3RefinedCarrierChild m i) M.nu _ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 _

/-- Exact finite-sum form of the refined start observable. -/
theorem nativeHeatRefinedObservable_eq_Gen (ns : ℕ)
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    nativeHeatRefinedObservableGen ns M m ω =
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex,
          (Cold.coldNativeCellTrace M (m + 1)
              (nativeHeatQ3RefinedCarrierChild m i) ω +
            2 * (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i *
              Variational.shearTraceLinear
                (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
                  (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
            nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2 *
              Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
                (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
                  (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight) := by
  unfold nativeHeatRefinedObservableGen
  rw [nativeHeat_childMeanTrace_constantShift_sum
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      nativeHeatQ3RefinedCarrierChild m i) M.nu _ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1]
  rw [Fintype.card_fin]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [nativeHeatRefined_childTrace_shift_eq]
  unfold nativeHeatQ3RefinedCarrierSourceZGen
  ring

/-- Pointwise, almost surely, the refined start observable is bounded by the
old average, the center quadratic, the shear cross and the rare quadratic. -/
theorem nativeHeatRefinedObservable_le_components_Gen (ns : ℕ)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m + 1, nativeInductionState M h n) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      nativeHeatRefinedObservableGen ns M m ω ≤
        nativeHeatRefinedOldAverage M m ω +
          2 * (nativeHeatB : ℝ) *
            nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen ns M m ω +
          nativeHeatQ3RefinedCarrierSourceShearCrossGen ns M m ω +
          nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen ns M m ω := by
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
  rw [nativeHeatRefinedObservable_eq_Gen]
  unfold nativeHeatRefinedOldAverage nativeHeatQ3RefinedCarrierSourceCenterQuadraticGen
    nativeHeatQ3RefinedCarrierSourceShearCrossGen
    nativeHeatQ3RefinedCarrierSourceRareQuadraticD4Gen
  set N : ℝ := (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  have hpt : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2 *
        Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
          (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
            (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight ≤
      2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2 +
        2 * nativeHeatOldInverseRemainderD4 M
          (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2 := by
    intro i
    have hsq := sq_nonneg (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i)
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
        2 * (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i *
          Variational.shearTraceLinear
            (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
        nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2 *
          Matrix.trace (frameMatrix (Annealed.sigmaBar M (m + 1) : ℝ)
            (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
              (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)).lowerRight) ≤
      N * ∑ i : nativeHeatQ3RefinedCarrierIndex,
        (Cold.coldNativeCellTrace M (m + 1) (nativeHeatQ3RefinedCarrierChild m i) ω +
          2 * (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i *
            Variational.shearTraceLinear
              (coarseBlockMatrix (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
                (Cutoff.coefficientCutoff M.nu (m + 1) ω).toFun)) +
          (2 * (nativeHeatB : ℝ) * nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2 +
            2 * nativeHeatOldInverseRemainderD4 M
              (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
              nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i ^ 2)) := by
    apply mul_le_mul_of_nonneg_left _ hN0
    exact Finset.sum_le_sum (fun i _ => by linarith [hpt i])
  refine key.trans (le_of_eq ?_)
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

end

end ASDExplicitGamma.Native
