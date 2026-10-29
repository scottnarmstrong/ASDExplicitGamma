module

public import ASDExplicitGamma.Main.HotCovNodeFinal
public import ASDExplicitGamma.Main.HotEOscillationPathwise
public import ASDExplicitGamma.Main.HotFeedbackBill
public import ASDExplicitGamma.Main.HotRemainderFeedbackNode
public import ASDExplicitGamma.Main.ELinearObsPathwise
public import ASDExplicitGamma.Native.HotTopCovarianceBill
public import ASDExplicitGamma.Native.OldSignedBottomCovarianceBill
public import ASDExplicitGamma.Native.OldSignedDirectionalFlatSignedAssembly
public import ASDExplicitGamma.Native.OldSignedGlobalMinusDirectionalFeedback
public import ASDExplicitGamma.Native.OldSignedHalfGainBill

/-! Generator assembly, step 1: the nine families of the hot-patched trial at an
observer root are summable and their series is the exact sum of the grouped rows. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational

noncomputable section

/-- Per-cell summability of the affine carrier modes of the hot trial. -/
theorem hotGen_aff_cell_summable (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1) (U : OldSignedCellIndex Q d) :
    Summable (fun n => hotCovAffMode Q d nu sigma hnu hsigma k b L n U) := by
  classical
  have hs := hasSum_sum (s := Finset.univ) (fun c _ =>
    (hotCov_cell_series_C Q d nu sigma hnu hsigma k b L hL hmesh U c).2)
  have he : (fun n => hotCovAffMode Q d nu sigma hnu hsigma k b L n U) =
      fun n => ∑ c : BlockCoord 2, hotCovAffCrossC Q d nu sigma hnu hsigma k b L c n U :=
    funext fun n => hotCovAffMode_eq_sum Q d nu sigma hnu hsigma k b L n U
  rw [he]
  exact hs.summable

/-- Per-cell summability of the oscillatory carrier modes of the hot trial. -/
theorem hotGen_osc_cell_summable (mm : ℤ) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 mm) d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (U : OldSignedCellIndex (originCube 2 mm) d) :
    Summable (fun n => hotCovOscMode (originCube 2 mm) d nu sigma hnu hsigma k b L n U) := by
  classical
  have hH : ∀ n P, MemBlockL2 (openCubeSet (originCube 2 mm))
      (hotPatchSource (originCube 2 mm) d d nu sigma hnu hsigma k b L n P) :=
    fun n P => hot_patch_source_memL2 _ d d nu sigma hnu hsigma k b L n P
  have hpos := fun n P U hU j => hot_source_positive_series (originCube 2 mm) d nu sigma hnu hsigma
    k b L n P U hU j
  have hsrc := fun U hU => hot_source_cell_summable mm d nu sigma hnu hsigma k b L hL U hU
  exact (main_e_actual_oscillatory_cross_2dq_hot (originCube 2 mm) d nu sigma hnu hsigma k b L
    (fun n P x => hotPatchSource (originCube 2 mm) d d nu sigma hnu hsigma k b L n P x) hH hpos hsrc
    U).1

/-- The nine families of the hot trial at an observer root are summable; the total series is the
exact sum of the grouped rows (linear group, boundary baseline, affine mean, source square,
covariance and oscillatory mixed carriers, source feedback, top and bottom covariance). -/
theorem hot_trial_total_hasSum (mm : ℤ) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 mm) d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius (originCube 2 mm) d * 3 ^ 6 ≤ L.1) :
    let Q := originCube 2 mm
    let a := responseFramePlanarCoefficientField nu sigma k
    let T := hotPatchTrialTerms Q d nu sigma hnu hsigma k b L
    HasSum T.total
      ((∑' n, (T.flat n - oldSignedFlatBoundaryModeEnergy Q b L n -
          oldSignedFlatAffineMode Q d a b L n + 2 * T.feedbackPlus n - 2 * T.feedbackMinus n)) +
        (∑' n, oldSignedFlatBoundaryModeEnergy Q b L n) +
        (∑' n, oldSignedFlatAffineMode Q d a b L n) +
        (∑' n, T.source n) +
        (hotCovAffCarrier Q d nu sigma hnu hsigma k b L +
          ∑' n, oldSignedCellAverage Q d (hotCovOscMode Q d nu sigma hnu hsigma k b L n)) +
        2 * (∑' n, T.feedbackSource n) + (∑' n, T.covarianceTop n) +
        ∑' n, T.covarianceBottom n) := by
  classical
  intro Q a T
  have hf := old_signed_flat_signed_energy_bill_directional Q d nu sigma hnu hsigma k b L
  change Summable T.flat ∧ _ at hf
  have hp := old_signed_global_plus_feedback_directional_bill_halfgain Q d nu sigma hnu hsigma k b L
  change Summable T.feedbackPlus ∧ _ at hp
  have hm := old_signed_global_minus_feedback_directional_bill Q d nu sigma hnu hsigma k b L
  change Summable T.feedbackMinus ∧ _ at hm
  have hB := (old_signed_flat_boundary_energy_trace Q b L).summable
  have hA := old_signed_flat_affine_summable Q d a b L
  have hS := hot_source_energy_bill mm d nu sigma hnu hsigma k b L hL
  change Summable T.source ∧ _ at hS
  have hFs := hot_source_feedback_bill mm d nu sigma hnu hsigma k b L hL
  change Summable T.feedbackSource ∧ _ at hFs
  have hTop : Summable T.covarianceTop ∧ _ :=
    hot_top_covariance_bill Q d nu sigma hnu hsigma k b L
  have hBot : Summable T.covarianceBottom ∧ _ :=
    old_signed_actual_bottom_covariance_bill Q d nu sigma hnu hsigma k b L
  have hAffC := old_signed_cell_average_series Q d
    (fun n U => hotCovAffMode Q d nu sigma hnu hsigma k b L n U)
    (fun U => hotGen_aff_cell_summable Q d nu sigma hnu hsigma k b L hL hmesh U)
  have hOscC := old_signed_cell_average_series Q d
    (fun n U => hotCovOscMode Q d nu sigma hnu hsigma k b L n U)
    (fun U => hotGen_osc_cell_summable mm d nu sigma hnu hsigma k b L hL U)
  have hAffV : hotCovAffCarrier Q d nu sigma hnu hsigma k b L =
      ∑' n, oldSignedCellAverage Q d (hotCovAffMode Q d nu sigma hnu hsigma k b L n) := rfl
  have hLsum : Summable (fun n => T.flat n - oldSignedFlatBoundaryModeEnergy Q b L n -
      oldSignedFlatAffineMode Q d a b L n + 2 * T.feedbackPlus n - 2 * T.feedbackMinus n) :=
    (((hf.1.sub hB).sub hA).add (hp.1.mul_left 2)).sub (hm.1.mul_left 2)
  have hmix : Summable (fun n => oldSignedCellAverage Q d (hotCovAffMode Q d nu sigma hnu hsigma k b L n) +
      oldSignedCellAverage Q d (hotCovOscMode Q d nu sigma hnu hsigma k b L n)) :=
    hAffC.1.add hOscC.1
  have hall := (((((((hLsum.hasSum.add hB.hasSum).add hA.hasSum).add hS.1.hasSum).add
    hmix.hasSum).add (hFs.1.hasSum.mul_left 2)).add hTop.1.hasSum).add hBot.1.hasSum)
  have hmixV : (∑' n, (oldSignedCellAverage Q d (hotCovAffMode Q d nu sigma hnu hsigma k b L n) +
      oldSignedCellAverage Q d (hotCovOscMode Q d nu sigma hnu hsigma k b L n))) =
      hotCovAffCarrier Q d nu sigma hnu hsigma k b L +
        ∑' n, oldSignedCellAverage Q d (hotCovOscMode Q d nu sigma hnu hsigma k b L n) := by
    rw [hAffV]; exact hAffC.1.tsum_add hOscC.1
  rw [hmixV] at hall
  convert hall using 1
  funext n
  have h := hotCov_trial_mixed_split Q d nu sigma hnu hsigma k b L n
  simp only [] at h
  simp only [OldSignedTrialTerms.total]
  linarith [h]

end

end ASDExplicitGamma.Main
