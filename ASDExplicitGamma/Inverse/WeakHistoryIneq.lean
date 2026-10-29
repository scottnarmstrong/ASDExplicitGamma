module

public import ASDExplicitGamma.Inverse.RawTraceSpatialAverage
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Inverse.RawWeakHistory
public import Mathlib.Analysis.SpecificLimits.Normed

/-! The weak-history envelope from the actual averaged traces. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable section

/-- The depthwise p=2 envelope supplied by the exact raw-shell transport. -/
def rawWeakTraceProfileEnvelope (M : ABKModel 2) (j : ℕ) : ℝ :=
  theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
    (3 : ℝ) ^ (6 * gammaZero * j)

private theorem raw_weak_trace_profile_envelope_nonneg_helper
    (M : ABKModel 2) (j : ℕ) :
    0 ≤ rawWeakTraceProfileEnvelope M j := by
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hMrat : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
  unfold rawWeakTraceProfileEnvelope
  positivity

private theorem raw_weak_trace_profile_envelope_summable_helper
    (M : ABKModel 2) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      rawWeakTraceProfileEnvelope M j) := by
  let α : ℝ := Scalar.inverseHistoryDiscount
  let q : ℝ := α * (3 : ℝ) ^ (6 * gammaZero)
  have hqeq : q = (3 : ℝ) ^ (6 * gammaZero - 1 / 4) := by
    dsimp [q, α, Scalar.inverseHistoryDiscount]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hq0 : 0 ≤ q := by
    rw [hqeq]
    positivity
  have hq1 : q < 1 := by
    rw [hqeq]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 3)
    norm_num [gammaZero]
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hq0]
    exact hq1
  have hgeom : Summable (fun j : ℕ => q ^ j) :=
    summable_geometric_of_lt_one hq0 hq1
  have hlin : Summable (fun j : ℕ => (j : ℝ) * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm
  have hquad : Summable (fun j : ℕ => (j : ℝ) ^ 2 * q ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 2 hqnorm
  have hpoly : Summable (fun j : ℕ => (1 + (j : ℝ)) ^ 2 * q ^ j) := by
    have hsum := hquad.add (hlin.mul_left 2)
    have hsum' := hsum.add hgeom
    apply hsum'.congr
    intro j
    ring
  have hpow (j : ℕ) :
      (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) =
        ((3 : ℝ) ^ (6 * gammaZero)) ^ j := by
    rw [show 6 * gammaZero * (j : ℝ) =
      (6 * gammaZero) * (j : ℝ) by ring]
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (6 * gammaZero)) j]
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hterm (j : ℕ) :
      Scalar.inverseHistoryDiscount ^ j * rawWeakTraceProfileEnvelope M j =
        (theta M * (invTraceM : ℚ)) *
          ((1 + (j : ℝ)) ^ 2 * q ^ j) := by
    rw [rawWeakTraceProfileEnvelope, hpow]
    dsimp [q]
    ring
  have hpoly' := hpoly.mul_left (theta M * (invTraceM : ℚ))
  exact hpoly'.congr fun j => (hterm j).symm

/-- Build the L² witnesses for the actual depth-average sequence from the
exact p=20 shell-transport conclusion and the ordinary native states. -/
theorem rawWeakTraceSequenceMemLpFromShellTransport
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField (closure (cubeSet
              (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + j))) :
    ∀ j : ℕ,
      MemLp
        (fun ω => rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j)
        2 (Cutoff.cutoffSampleLaw M).toMeasure := by
  intro j
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m r hr t ht hstate hShell j
  have hU : 0 ≤ rawWeakTraceProfileEnvelope M j :=
    raw_weak_trace_profile_envelope_nonneg_helper M j
  apply memLp_iff.mpr
  simpa [rawWeakTraceProfileEnvelope] using
    hprofile.trans_lt ENNReal.ofReal_lt_top

/-- Under the exact shell premise, the normalized actual weak history has
an L² envelope obtained by summing the p=2 depth profile. -/
theorem raw_weak_trace_history_norm_of_shell_transport_helper
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField (closure (cubeSet
              (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + j))) :
    let Q := originCube 2 (m - (r : ℤ))
    let hT := rawWeakTraceSequenceMemLpFromShellTransport
      M h hγ m r hr t ht hstate hShell
    ‖rawWeakTraceHistoryLp M m Q t hT‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          rawWeakTraceProfileEnvelope M j := by
  let Q := originCube 2 (m - (r : ℤ))
  let hT := rawWeakTraceSequenceMemLpFromShellTransport
    M h hγ m r hr t ht hstate hShell
  have hU : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      rawWeakTraceProfileEnvelope M j) :=
    raw_weak_trace_profile_envelope_summable_helper M
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m r hr t ht hstate hShell
  have hbound (j : ℕ) :
      ‖(hT j).toLp
          (rawWeakTraceSequence M m Q t · j)‖ ≤
        rawWeakTraceProfileEnvelope M j := by
    have hUj := raw_weak_trace_profile_envelope_nonneg_helper M j
    have hprofilej :
        eLpNorm (rawWeakTraceSequence M m Q t · j) 2
          (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
      simpa [rawWeakTraceProfileEnvelope] using hprofile j
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprofilej
    rw [ENNReal.toReal_ofReal hUj] at hreal
    rw [Lp.norm_toLp]
    exact hreal
  exact raw_weak_trace_history_lpNorm_le_of_envelope M m Q t hT
    (rawWeakTraceProfileEnvelope M) hU hbound

private theorem raw_weak_trace_inserted_elliptic_cube_helper
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2)
    (Q : TriadicCube 2) :
    ∃ Lam : ℝ,
      IsEllipticFieldOn M.nu Lam (openCubeSet Q)
        (Model.partialInsertedCoefficient M m t ω).toFun := by
  let K := closure (cubeSet Q)
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  let Lam : ℝ := ((2 : ℝ) * 2 *
    (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu
  refine ⟨Lam, ?_⟩
  simpa [Lam] using
    (Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω
      ⟨ht.1, ht.2⟩ (measurableSet_openCubeSet Q)
      (fun _ hx => hK (subset_closure
        (openCubeSet_subset_cubeSet Q hx))))

private theorem raw_weak_trace_sequence_weighted_summable_ae_helper
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField (closure (cubeSet
              (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + j))) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
        rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j) := by
  let Q := originCube 2 (m - (r : ℤ))
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    rawWeakTraceSequence M m Q t ω j
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => α ^ j * T j ω
  let hT := rawWeakTraceSequenceMemLpFromShellTransport
    M h hγ m r hr t ht hstate hShell
  have hα := Scalar.inverse_history_discount_range
  have hU : Summable (fun j : ℕ => α ^ j * rawWeakTraceProfileEnvelope M j) := by
    simpa [α] using raw_weak_trace_profile_envelope_summable_helper M
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m r hr t ht hstate hShell
  have hFmem (j : ℕ) : MemLp (F j) 2 μ := by
    have hTj : MemLp (T j) 2 μ := by
      simpa [T, Q, μ] using hT j
    change MemLp ((α ^ j) • T j) 2 μ
    exact hTj.const_smul (α ^ j)
  have hFbound (j : ℕ) : lpNorm (F j) 2 μ ≤
      α ^ j * rawWeakTraceProfileEnvelope M j := by
    have hUj := raw_weak_trace_profile_envelope_nonneg_helper M j
    have hαj : 0 ≤ α ^ j := pow_nonneg hα.1.le j
    have hprofilej : eLpNorm (T j) 2 μ ≤
        ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) := by
      simpa [T, Q, rawWeakTraceProfileEnvelope] using hprofile j
    have hscaled : eLpNorm (F j) 2 μ ≤
        ENNReal.ofReal (α ^ j * rawWeakTraceProfileEnvelope M j) := by
      have hFfun : F j = (α ^ j) • T j := by
        funext ω
        rfl
      calc
        eLpNorm (F j) 2 μ =
            ENNReal.ofReal (α ^ j) * eLpNorm (T j) 2 μ := by
          rw [hFfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hαj]
        _ ≤ ENNReal.ofReal (α ^ j) *
            ENNReal.ofReal (rawWeakTraceProfileEnvelope M j) :=
          mul_le_mul_of_nonneg_left hprofilej
            (by positivity)
        _ = ENNReal.ofReal
            (α ^ j * rawWeakTraceProfileEnvelope M j) :=
          (ENNReal.ofReal_mul hαj).symm
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hscaled
    rw [ENNReal.toReal_ofReal (mul_nonneg hαj hUj)] at hreal
    rw [← toReal_eLpNorm]
    exact hreal
  have hnormSummable : Summable (fun j : ℕ => lpNorm (F j) 2 μ) :=
    Summable.of_nonneg_of_le (fun j => lpNorm_nonneg)
      hFbound hU
  have hnormSumFinite :
      (∑' j : ℕ, eLpNorm (F j) 2 μ) ≠ ∞ := by
    have hsumEq : (∑' j : ℕ, eLpNorm (F j) 2 μ) =
        ∑' j : ℕ, ENNReal.ofReal (lpNorm (F j) 2 μ) := by
      apply tsum_congr
      intro j
      exact (ofReal_lpNorm (hFmem j)).symm
    rw [hsumEq]
    exact ne_of_lt hnormSummable.tsum_ofReal_lt_top
  have hpoint := summable_norm_of_tsum_eLpNorm_ne_top
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hnormSumFinite
  have hTnonneg (ω : Cutoff.CutoffSample 2) (j : ℕ) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  filter_upwards [hpoint] with ω hω
  apply hω.congr
  intro j
  change |α ^ j * T j ω| = α ^ j * T j ω
  exact abs_of_nonneg
    (mul_nonneg (pow_nonneg hα.1.le j) (hTnonneg ω j))

/-- The pathwise inverse-history inequality for the actual averaged
trace sequence, paired with the shell-derived OLD-law L² envelope. The finite
root family is source data; its depth discount is derived from Lemma V. -/
theorem raw_weak_trace_inequality_of_shell_transport_helper
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField (closure (cubeSet
              (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + j))) :
    let Q := originCube 2 (m - (r : ℤ))
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let a : Cutoff.CutoffSample 2 → CoeffField 2 := fun ω =>
      (Model.partialInsertedCoefficient M m t ω).toFun
    let T : Cutoff.CutoffSample 2 → ℕ → ℝ := fun ω j =>
      rawWeakTraceSequence M m Q t ω j
    (∀ᵐ ω ∂μ,
      rawWeakTraceProxy
          (fun j => rawFiniteInverseDepthMax s (a ω)
            (Annealed.sigmaBar M m : ℝ) j)
          (T ω) ≤
        (1 + Scalar.inverseHistoryDiscount) *
          rawFiniteInverseHistoryMax s (a ω)
            (Annealed.sigmaBar M m : ℝ) * rawWeakTraceHistory (T ω)) ∧
    (‖rawWeakTraceHistoryLp M m Q t
        (rawWeakTraceSequenceMemLpFromShellTransport
          M h hγ m r hr t ht hstate hShell)‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          rawWeakTraceProfileEnvelope M j) := by
  let Q := originCube 2 (m - (r : ℤ))
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a : Cutoff.CutoffSample 2 → CoeffField 2 := fun ω =>
    (Model.partialInsertedCoefficient M m t ω).toFun
  let T : Cutoff.CutoffSample 2 → ℕ → ℝ := fun ω j =>
    rawWeakTraceSequence M m Q t ω j
  let hT := rawWeakTraceSequenceMemLpFromShellTransport
    M h hγ m r hr t ht hstate hShell
  have hα := Scalar.inverse_history_discount_range
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hσ0 : 0 ≤ σ := hσ.le
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m r hr t ht hstate hShell
  have hU : Summable (fun j : ℕ => α ^ j *
      rawWeakTraceProfileEnvelope M j) := by
    simpa [α] using raw_weak_trace_profile_envelope_summable_helper M
  have hdepth : ∀ᵐ ω ∂μ, ∀ j,
      α ^ j * rawFiniteInverseDepthMax s (a ω) σ j ≤
        rawFiniteInverseHistoryMax s (a ω) σ := by
    filter_upwards with ω
    intro j
    change α ^ j * Book.Ch02.finsetSupReal s
        (fun Q => σ * lemmaVInverseDepthMax Q (a ω) j) ≤ _
    rw [← Scalar.inverse_history_finset_max_mul s hs
      (fun Q => σ * lemmaVInverseDepthMax Q (a ω) j) (α ^ j)
      (pow_pos hα.1 j)]
    change Book.Ch02.finsetSupReal s
        (fun Q => α ^ j * (σ * lemmaVInverseDepthMax Q (a ω) j)) ≤
      Book.Ch02.finsetSupReal s
        (fun Q => σ * lemmaVInverseHistory Q (a ω)
          ((3 : ℝ) ^ (1 / 4 : ℝ)))
    apply Book.Ch02.finsetSupReal_le _ hs
    intro Q hQ
    obtain ⟨Lam, hEll⟩ := raw_weak_trace_inserted_elliptic_cube_helper
      M m t ht ω Q
    have hlocal := actual_inverse_depth_discount_bound Q (a ω) hEll σ hσ0 j
    have hglobal : σ * lemmaVInverseHistory Q (a ω)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        Book.Ch02.finsetSupReal s
          (fun R => σ * lemmaVInverseHistory R (a ω)
            ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
      unfold Book.Ch02.finsetSupReal
      exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨Q, hQ, rfl⟩
    exact hlocal.trans hglobal
  have hTnonneg (ω : Cutoff.CutoffSample 2) (j : ℕ) : 0 ≤ T ω j := by
    exact raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  have hTrace : ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      α ^ j * rawWeakTraceSequence M m Q t ω j) := by
    simpa [α, T] using raw_weak_trace_sequence_weighted_summable_ae_helper
      M h hγ m r hr t ht hstate hShell
  have hdepthMax0 (ω : Cutoff.CutoffSample 2) (j : ℕ) :
      0 ≤ rawFiniteInverseDepthMax s (a ω) σ j := by
    apply Book.Ch02.finsetSupReal_nonneg
    intro R _
    exact mul_nonneg hσ0 (lemmaVInverseDepthMax_nonneg R (a ω) j)
  have hhistory0 (ω : Cutoff.CutoffSample 2) :
      0 ≤ rawFiniteInverseHistoryMax s (a ω) σ := by
    apply Book.Ch02.finsetSupReal_nonneg
    intro R _
    exact mul_nonneg hσ0
      (lemmaVInverseHistory_nonneg R (a ω) hq)
  have hProxy : ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      α ^ (2 * j) * rawFiniteInverseDepthMax s (a ω) σ j * T ω j) := by
    filter_upwards [hdepth, hTrace] with ω hdepthω hTraceω
    let B := rawFiniteInverseHistoryMax s (a ω) σ
    have hterm (j : ℕ) :
        α ^ (2 * j) * rawFiniteInverseDepthMax s (a ω) σ j * T ω j ≤
          B * (α ^ j * T ω j) := by
      calc
        _ = (α ^ j * rawFiniteInverseDepthMax s (a ω) σ j) *
            (α ^ j * T ω j) := by
          rw [show 2 * j = j + j by omega, pow_add]
          ring
        _ ≤ B * (α ^ j * T ω j) :=
          mul_le_mul_of_nonneg_right (hdepthω j)
            (mul_nonneg (pow_nonneg hα.1.le j) (hTnonneg ω j))
    have hsum : Summable (fun j : ℕ => B * (α ^ j * T ω j)) :=
      hTraceω.mul_left B
    apply Summable.of_nonneg_of_le
      (fun j => mul_nonneg
        (mul_nonneg (pow_nonneg hα.1.le (2 * j)) (hdepthMax0 ω j))
        (hTnonneg ω j)) hterm hsum
  have hproxyResult := raw_weak_trace_proxy_le_ae μ
    (fun ω j => rawFiniteInverseDepthMax s (a ω) σ j) T
    (fun ω => rawFiniteInverseHistoryMax s (a ω) σ)
    hdepth (by filter_upwards with ω; exact hTnonneg ω)
    hProxy hTrace
  have hnorm := raw_weak_trace_history_norm_of_shell_transport_helper
    M h hγ m r hr t ht hstate hShell
  refine ⟨?_, ?_⟩
  · simpa [Q, μ, a, T, α, σ] using hproxyResult
  · simpa [Q] using hnorm

/-- IN-WEAK-HISTORY-INEQUALITY. The exact shell family is
constructed from the p=20 theorem and the native states in the result's local
definition, so the pathwise inequality and OLD-law history norm carry no
shell-transport premise. -/
theorem raw_weak_trace_inequality_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ))) :
    let hShell := raw_trace_transport_shell_family_source
      M h hM hγ m r t ht hstate
    let Q := originCube 2 (m - (r : ℤ))
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let a : Cutoff.CutoffSample 2 → CoeffField 2 := fun ω =>
      (Model.partialInsertedCoefficient M m t ω).toFun
    let T : Cutoff.CutoffSample 2 → ℕ → ℝ := fun ω j =>
      rawWeakTraceSequence M m Q t ω j
    (∀ᵐ ω ∂μ,
      rawWeakTraceProxy
          (fun j => rawFiniteInverseDepthMax s (a ω)
            (Annealed.sigmaBar M m : ℝ) j)
          (T ω) ≤
        (1 + Scalar.inverseHistoryDiscount) *
          rawFiniteInverseHistoryMax s (a ω)
            (Annealed.sigmaBar M m : ℝ) * rawWeakTraceHistory (T ω)) ∧
    (‖rawWeakTraceHistoryLp M m Q t
        (rawWeakTraceSequenceMemLpFromShellTransport
          M h hγ m r hr t ht hstate hShell)‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          rawWeakTraceProfileEnvelope M j) := by
  let hShell := raw_trace_transport_shell_family_source
    M h hM hγ m r t ht hstate
  exact raw_weak_trace_inequality_of_shell_transport_helper
    M h hγ m r hr t ht s hs hstate hShell

end
end ASDExplicitGamma.Inverse
