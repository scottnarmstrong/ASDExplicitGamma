/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualHyp
public import ASDExplicitGamma.Scalar.SmoothFeedbackForcedFeedback
public import ASDExplicitGamma.Scalar.SmoothFeedbackFwMeasurable
public import ASDExplicitGamma.Scalar.SmoothFeedbackMaximizerExists

/-! The smooth-feedback estimate `Λ₈` (SC-SMOOTH-FEEDBACK-GAP) on the actual
OLD objects: the pathwise identities and bounds, the annealed charges, and the
one-load consumer. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Identity

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- The lift `Z_lift,i`: the finite patch of the actual cell residuals of the top load. -/
def topLift (ω : Cutoff.CutoffSample 2) (i : ι) : Vec 2 → BlockVec 2 :=
  oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
    (topLoad Q u i) (topLoad_memL2 Q u i)

/-- `Σ_l ⟨w_l, p_lift,l⟩`. -/
def plift' (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  scalarSourcePairing (openCubeSet Q) (fun x => (u i).toH1Function.grad x)
    (topLift M m Q depth u ω i)

/-- `N = Σ_l ‖Z*_l‖²_A`. -/
def nmax' (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (ω : Cutoff.CutoffSample 2) : ℝ := ∑ i ∈ S,
  scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) (Z ω i)

/-- Λ8.1: `Gap = E_lift - 2 Σ_l ⟨w_l, p_lift,l⟩ + N ≥ 0`. -/
theorem actual_gap_identity
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    (ω : Cutoff.CutoffSample 2) :
    gap' S M m Q depth u Z ω = elift S M m Q depth u ω - 2 * plift' S M m Q depth u ω +
        nmax' S M m Q Z ω ∧ 0 ≤ gap' S M m Q depth u Z ω := by
  classical
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  refine ⟨?_, ?_⟩
  · unfold gap' elift plift' nmax'
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hW : ScalarVariation (openCubeSet Q) (topLoad Q u i) :=
      ⟨topLoad_memL2 Q u i, by simpa [topLoad] using (u i).isPotentialZeroTraceOn,
        isSolenoidalZeroNormalTraceOn_zero⟩
    have hid := smooth_feedback_actual_local_lift_gap_identity Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω)
      (fun x => (u i).toH1Function.grad x) hW (Z ω i) (hZ ω i)
    dsimp only at hid
    have hTop : scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω) (topLift M m Q depth u ω i) =
        oldSignedCellAverage Q depth (fun U =>
          oldSignedEnergyPairing U.val M.nu (Annealed.sigmaBar M m : ℝ)
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              (oldCutoffSkewCoefficient m Q ω))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
              (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property
              (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad_memL2 Q u i))) := by
      rw [scalarFieldEnergy_eq_pairing Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ]
      exact old_signed_local_residual_cell_pairing Q depth M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω) (topLoad Q u i) (topLoad Q u i)
        (topLoad_memL2 Q u i) (topLoad_memL2 Q u i)
    rw [← hTop]
    exact hid
  · exact Finset.sum_nonneg fun i _ =>
      smooth_feedback_scalar_field_energy_nonneg Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos hσ _ _

end Identity

section Annealed

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- `E A_pair = Σ_{l,U}' (E T_U / 2) |w_{l,U}|²`. -/
theorem Apair_expectation :
    (∫ ω, apair S M m Q depth u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∑ i ∈ S, oldSignedCellAverage Q depth (fun U =>
        (1 / 2 : ℝ) * (∫ ω, smoothFeedbackCellT M m U.val ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) * vecNormSq (cellMean Q u i U.val)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hfun : apair S M m Q depth u = fun ω => ∑ i ∈ S, ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ U : OldSignedCellIndex Q depth,
        smoothFeedbackPairCharge M m U.val (cellMean Q u i U.val) ω := by
    funext ω
    unfold apair oldSignedCellAverage
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun U _ => ?_
    exact cell_pair_eq M m Q depth U ω _
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    unfold oldSignedCellAverage
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun U _ => ?_
      exact smooth_feedback_cell_mean_pair_quadratic M m U.val _
    · intro U _
      exact smooth_feedback_cell_pair_charge_integrable M m U.val _
  · intro i _
    refine (integrable_finsetSum _ fun U _ => ?_).const_mul _
    exact smooth_feedback_cell_pair_charge_integrable M m U.val _

end Annealed

section Node

variable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
  (depth : ℕ) (u : ι → H10Function (openCubeSet Q))

/-- The source's `G_pair`. -/
def gpair
    (hcenter : ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)))
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  apair S M m Q depth u ω + 2 * Real.sqrt (pK' S M m Q depth u ω * rK' S M m Q depth u ω) +
    rK' S M m Q depth u ω +
    2 * Real.sqrt (pD S M m Q depth u ω * rD S M m Q depth u hcenter ω) +
    rD S M m Q depth u hcenter ω +
    2 * Real.sqrt (deltaSq' S Q depth u) *
      (Real.sqrt (bhist M m Q depth ω *
        (Real.sqrt (pK' S M m Q depth u ω) + Real.sqrt (rK' S M m Q depth u ω)) ^ 2) +
        Real.sqrt (omega2 S Q u))

theorem FwStar_nonneg (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ fwStar S M m Q depth u Z ω :=
  Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q depth _ fun U =>
    add_nonneg (vectorWeakHaarEnergy_nonneg _ _) (vectorWeakHaarEnergy_nonneg _ _)

/-- **SC-SMOOTH-FEEDBACK-GAP**, the smooth-feedback estimate `Λ₈`, on the actual objects:
the OLD cutoff law of the shell `k = m + 1`, the OLD maximizers `Z*_l` of the loads
`w_l`, the actual child cells of side `m - 5` of `Q_{m+129}`, the actual local
inverse histories and the OLD bank.

The pathwise block is Λ8.1–Λ8.4 and the Gram trace bound; the annealed block is
Λ8.5–Λ8.6 with `a₅ = mainSourceMeanPrefix`, `ξ = Ξ₀` of the shell `k`; the consumer
block is the one-load estimate with `ω = 1/2`, `δ_n = lambda8DeltaN`, `m_*`, `b`, `ε`.
The only inputs are the standing assumptions, the earlier-label states, and
`Ω² ≤ ω v`, `δ² ≤ δ_n² v`. -/
theorem sc_smooth_feedback_gap {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (Q : TriadicCube 2) (hQ : Q = originCube 2 (m + 129))
    (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    {v : ℝ} (hv : 0 ≤ v)
    (hOm : omega2 S Q u ≤ (1 / 2) * v)
    (hds : deltaSq' S Q 134 u ≤ lambda8DeltaN ^ 2 * v) :
    -- pathwise conclusions
    (∀ ω : Cutoff.CutoffSample 2,
      (gap' S M m Q 134 u Z ω = elift S M m Q 134 u ω - 2 * plift' S M m Q 134 u ω +
          nmax' S M m Q Z ω ∧ 0 ≤ gap' S M m Q 134 u Z ω) ∧
      (0 ≤ apair S M m Q 134 u ω ∧
        apair S M m Q 134 u ω ≤ ∑ i ∈ S, oldSignedCellAverage Q 134 (fun U =>
          smoothFeedbackCellT M m U.val ω * vecNormSq (cellMean Q u i U.val)) ∧
        gap' S M m Q 134 u Z ω ≤ gpair S M m Q 134 u (hcenter'' Q u H 134) ω) ∧
      Real.sqrt (fwDiff S M m Q 134 u Z ω) ≤
        Real.sqrt (bhist M m Q 134 ω * gap' S M m Q 134 u Z ω) +
          Scalar.inverseHistoryDiscount * bhist M m Q 134 ω *
            Real.sqrt (deltaSq' S Q 134 u) ∧
      Real.sqrt (fwStar S M m Q 134 u Z ω) ≤
        Real.sqrt (theta'' S M m Q 134 u ω) +
          Real.sqrt (bhist M m Q 134 ω * rK' S M m Q 134 u ω) +
          Real.sqrt (bhist M m Q 134 ω * gap' S M m Q 134 u Z ω) +
          (1 + Scalar.inverseHistoryDiscount * bhist M m Q 134 ω) *
            Real.sqrt (deltaSq' S Q 134 u)) ∧
    -- the Gram bound (trace form, for every cell)
    (∀ (ω : Cutoff.CutoffSample 2) (U : TriadicCube 2),
      smoothFeedbackCellDirectionalGammaTrace M m U ω ≤
        Inverse.rawWeakTraceProxy
          (fun j => lemmaVInverseDepthMax U
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m U ω)) j)
          (fun j => descendantsAverage U j (fun R => traceDefect (openCubeSet R)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m U ω)) 1))) ∧
    -- annealed conclusions
    ((∫ ω, apair S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∑ i ∈ S, oldSignedCellAverage Q 134 (fun U =>
          (1 / 2 : ℝ) * (∫ ω, smoothFeedbackCellT M m U.val ω
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) * vecNormSq (cellMean Q u i U.val)) ∧
      (∫ ω, apair S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainSourceMeanPrefix / 2 * omega2 S Q u ∧
      (∫ ω, pK' S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (1 + mainSourceMeanPrefix / 2) * omega2 S Q u ∧
      (∫ ω, pD S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (1 + mainSourceMeanPrefix / 2) * omega2 S Q u ∧
      (∫ ω, theta'' S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        xi'' M h m / 2 * omega2 S Q u) ∧
    -- the one-load consumer
    ((∫ ω, gap' S M m Q 134 u Z ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        v * gapEps mainSourceMeanPrefix (1 / 2) lambda8DeltaN (mStar' M)
          (14103 / 10000) (5 / 10 ^ 24) (76 / 100) ∧
      (∫ ω, bhist M m Q 134 ω * gap' S M m Q 134 u Z ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        v * (14103 / 10000 * gapEps mainSourceMeanPrefix (1 / 2) lambda8DeltaN
            (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (76 / 100) +
          5 / 10 ^ 24 * graW (mStar' M) (1 / 2) lambda8DeltaN (14103 / 10000) (76 / 100)) ∧
      (∫ ω, fwStar S M m Q 134 u Z ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        v * consumerL mainSourceMeanPrefix (xi'' M h m) (1 / 2)
          lambda8DeltaN (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (76 / 100) (76 / 100) ^ 2) := by
  classical
  have Hyp := actual_consumer_hyp S M h hM hγ m hpast Q hQ u H Z hZ hv hOm hds
  have hdisc := inverseHistoryDiscount_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    refine ⟨actual_gap_identity S M m Q 134 u Z hZ ω,
      ⟨Apair_nonneg S M m Q 134 u ω, Apair_le_trace S M m Q 134 u ω, ?_⟩,
      actual_forced_difference S M m Q 134 u H Z hZ ω,
      actual_fw_star_le S M m Q 134 u H Z hZ ω⟩
    exact actual_gap_le_gpair S M m Q 134 u H
      (fun i U hU => (smooth_feedback_h2_projected_source_admissible Q U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (u i) (H i)).2.1)
      (hcenter'' Q u H 134) Z hZ ω
  · intro ω U
    exact smooth_feedback_directional_gamma_trace_le_raw_trace_proxy M m U ω
  · refine ⟨Apair_expectation S M m Q 134 u, Hyp.eAp, Hyp.ePK, Hyp.ePD, Hyp.eTh⟩
  · refine ⟨consumer_gap Hyp, (consumer_BGap Hyp).2, ?_⟩
    refine consumer_Fw Hyp (c0 := 76 / 100) (by norm_num)
      (FwStar_measurable S M m Q 134 u Z hZ) (FwStar_nonneg S M m Q 134 u Z) ?_
    intro ω
    have h1 := actual_fw_star_le S M m Q 134 u H Z hZ ω
    have hB0 := Bhist_nonneg M m Q 134 ω
    have hs0 := Real.sqrt_nonneg (deltaSq' S Q 134 u)
    refine h1.trans ?_
    have : (1 + Scalar.inverseHistoryDiscount * bhist M m Q 134 ω) *
        Real.sqrt (deltaSq' S Q 134 u) ≤
        (1 + 76 / 100 * bhist M m Q 134 ω) * Real.sqrt (deltaSq' S Q 134 u) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hs0
    linarith

end Node

/-- The actual OLD maximizers of a finite family of loads. -/
def oldMaxFam {ι : Type*} (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (u : ι → H10Function (openCubeSet Q)) (ω : Cutoff.CutoffSample 2) (i : ι) :
    Vec 2 → BlockVec 2 :=
  oldMaximizer M m Q (fun x => (u i).toH1Function.grad x)
    (u i).toH1Function.grad_memVectorL2 ω

theorem oldMaxFam_spec {ι : Type*} (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (u : ι → H10Function (openCubeSet Q)) (ω : Cutoff.CutoffSample 2) (i : ι) :
    IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
      (fun x => (u i).toH1Function.grad x) (oldMaxFam M m Q u ω i) :=
  oldMaximizer_spec M m Q _ _ ω

/-- The actual maximizers are measurable in the OLD sample (as `L²` classes), and so is `F_w²`. -/
theorem oldMaxFam_measurable {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (depth : ℕ) (u : ι → H10Function (openCubeSet Q)) (i : ι) :
    Measurable (fun ω => toHilbertBlockL2OfBlockField
      (oldMaxFam_spec M m Q u ω i).1.1) ∧
    Measurable (fwStar S M m Q depth u (oldMaxFam M m Q u)) :=
  ⟨maximizer_class_measurable M m Q _ (u i).toH1Function.grad_memVectorL2
    (fun ω => oldMaxFam M m Q u ω i) (fun ω => oldMaxFam_spec M m Q u ω i),
   FwStar_measurable S M m Q depth u _ (oldMaxFam_spec M m Q u)⟩

section Modes

/-- The weak Hessian of the actual q3 mode loads. -/
def modeHessian (M : ABKModel 2) (h : ℝ) (e : Vec 2) (m : ℤ)
    (n : whiteBasisIndex) :
    HasWeakHessianOn (openCubeSet (originCube 2 (m + 1 + 128)))
      (lambda8Q3ParentModePotential M h e (m + 1) n).toH1Function :=
  lambda8Q3GaussianModeParentHessian (originCube 2 (m + 1 + 128)) _ _ _ n

/-- **SC-SMOOTH-FEEDBACK-GAP** for the actual q3 shell loads `w_n = -P_{D,Q}(ψ_n J e)`,
with `Ω² ≤ v/2` and `δ² ≤ δ_n² v` supplied by the load inputs
(SC-LAMBDA8-LOAD-INPUTS), `v = h² 3^{2γ(m+1)}`. -/
theorem sc_smooth_feedback_gap_modes (S : Finset whiteBasisIndex)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) :
    -- pathwise conclusions
    (∀ ω : Cutoff.CutoffSample 2,
      (gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω = elift S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω - 2 * plift' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω +
          nmax' S M m (originCube 2 (m + 1 + 128)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω ∧ 0 ≤ gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω) ∧
      (0 ≤ apair S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ∧
        apair S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ≤ ∑ i ∈ S, oldSignedCellAverage (originCube 2 (m + 1 + 128)) 134 (fun U =>
          smoothFeedbackCellT M m U.val ω * vecNormSq (cellMean (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1)) i U.val)) ∧
        gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω ≤ gpair S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (hcenter'' (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1)) (modeHessian M h e m) 134) ω) ∧
      Real.sqrt (fwDiff S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω) ≤
        Real.sqrt (bhist M m (originCube 2 (m + 1 + 128)) 134 ω * gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω) +
          Scalar.inverseHistoryDiscount * bhist M m (originCube 2 (m + 1 + 128)) 134 ω *
            Real.sqrt (deltaSq' S (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1))) ∧
      Real.sqrt (fwStar S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω) ≤
        Real.sqrt (theta'' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω) +
          Real.sqrt (bhist M m (originCube 2 (m + 1 + 128)) 134 ω * rK' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω) +
          Real.sqrt (bhist M m (originCube 2 (m + 1 + 128)) 134 ω * gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω) +
          (1 + Scalar.inverseHistoryDiscount * bhist M m (originCube 2 (m + 1 + 128)) 134 ω) *
            Real.sqrt (deltaSq' S (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)))) ∧
    -- the Gram bound (trace form, for every cell)
    (∀ (ω : Cutoff.CutoffSample 2) (U : TriadicCube 2),
      smoothFeedbackCellDirectionalGammaTrace M m U ω ≤
        Inverse.rawWeakTraceProxy
          (fun j => lemmaVInverseDepthMax U
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m U ω)) j)
          (fun j => descendantsAverage U j (fun R => traceDefect (openCubeSet R)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m U ω)) 1))) ∧
    -- annealed conclusions
    ((∫ ω, apair S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∑ i ∈ S, oldSignedCellAverage (originCube 2 (m + 1 + 128)) 134 (fun U =>
          (1 / 2 : ℝ) * (∫ ω, smoothFeedbackCellT M m U.val ω
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) * vecNormSq (cellMean (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1)) i U.val)) ∧
      (∫ ω, apair S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainSourceMeanPrefix / 2 * omega2 S (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1)) ∧
      (∫ ω, pK' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (1 + mainSourceMeanPrefix / 2) * omega2 S (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1)) ∧
      (∫ ω, pD S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (1 + mainSourceMeanPrefix / 2) * omega2 S (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1)) ∧
      (∫ ω, theta'' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        xi'' M h m / 2 * omega2 S (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ∧
    -- the one-load consumer
    ((∫ ω, gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ))) * gapEps mainSourceMeanPrefix (1 / 2) lambda8DeltaN (mStar' M)
          (14103 / 10000) (5 / 10 ^ 24) (76 / 100) ∧
      (∫ ω, bhist M m (originCube 2 (m + 1 + 128)) 134 ω * gap' S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ))) * (14103 / 10000 * gapEps mainSourceMeanPrefix (1 / 2) lambda8DeltaN
            (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (76 / 100) +
          5 / 10 ^ 24 * graW (mStar' M) (1 / 2) lambda8DeltaN (14103 / 10000) (76 / 100)) ∧
      (∫ ω, fwStar S M m (originCube 2 (m + 1 + 128)) 134 (lambda8Q3ParentModePotential M h e (m + 1)) (oldMaxFam M m (originCube 2 (m + 1 + 128)) (lambda8Q3ParentModePotential M h e (m + 1))) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ))) * consumerL mainSourceMeanPrefix (xi'' M h m) (1 / 2)
          lambda8DeltaN (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (76 / 100) (76 / 100) ^ 2):= by
  have hin := lambda8_mode_family_inputs M h hM e he (m + 1) S
  dsimp only at hin
  have hQeq : originCube 2 (m + 1 + 128) = originCube 2 (m + 129) := by
    congr 1; ring
  exact sc_smooth_feedback_gap S M h hM hγ m hpast (originCube 2 (m + 1 + 128)) hQeq
    (lambda8Q3ParentModePotential M h e (m + 1)) (modeHessian M h e m) _
    (fun ω n => oldMaximizer_spec M m (originCube 2 (m + 1 + 128))
      (fun x => (lambda8Q3ParentModePotential M h e (m + 1) n).toH1Function.grad x)
      (lambda8Q3ParentModePotential M h e (m + 1) n).toH1Function.grad_memVectorL2 ω)
    (by positivity) hin.1 hin.2

end Modes

end

end ASDExplicitGamma.Scalar
