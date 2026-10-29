/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.HistorySum
public import ASDExplicitGamma.AllOrder.CirFiniteEvenInduction
public import ASDExplicitGamma.AllOrder.CirFiniteEvenStepTransport
public import ASDExplicitGamma.AllOrder.ProfileResetAdapter
public import ASDExplicitGamma.AllOrder.CirResetTrace
public import ASDExplicitGamma.Main.FrameMap
public import ASDExplicitGamma.Inverse.BankHistoryPhysical

/-! # The real-order trace bound at every descendant depth -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

noncomputable section

private theorem aoPerDepth_trace_nonneg (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    0 ≤ traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ) := by
  obtain ⟨Λ, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
  exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos
    hEll (Annealed.sigmaBar_characterization M m).1

private theorem aoPerDepth_cell_reset_profile
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (Q : TriadicCube 2) (m : ℤ) (hQ : Q.scale ≤ m)
    (q : ℝ) (hq : 2 ≤ q) :
    eLpNorm (fun ω => ENNReal.ofReal
      (traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Inverse.orderTraceProfile M.gamma q
        (((m - Q.scale + 1 : ℤ) : ℝ))
        (|((m - Q.scale + 1 : ℤ) : ℝ)|)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let weights := aoCirStepWeights m (1 : ℝ)
  have hprofile := aoCir_step_profile_of_reset reset M h hM hγ hstate
    Q m m hQ q hq 1 (by norm_num) (by norm_num)
  let old := protectedOldLabel Q.scale (orderBand q)
  have hOld : old < m := by
    dsimp [old, protectedOldLabel]
    omega
  have hcoeff (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M old m weights ω =
        Cutoff.coefficientCutoff M.nu m ω := by
    change attenuatedCoefficient M old m (aoCirStepWeights m 1) ω = _
    ext x i j
    rw [aoCir_step_coefficient M old m hOld 1 ω x]
    have hentry := congrArg (fun a : RegCoeffField 2 => a.toFun x i j)
      (Main.mainInsertion_coefficient_one M (m - 1) ω)
    simpa only [show m - 1 + 1 = m by omega] using hentry
  have hroot (ω : Cutoff.CutoffSample 2) :
      rootTraceObservable M Q old m m weights ω =
        traceDefect (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu m ω).toFun
          (Annealed.sigmaBar M m : ℝ) + 4 := by
    rw [root_trace_observable_eq_trace_defect, hcoeff]
  have hrootNonneg : ∀ ω, 0 ≤ rootTraceObservable M Q old m m weights ω := by
    intro ω
    rw [hroot ω]
    have hdef := aoPerDepth_trace_nonneg M m Q ω
    linarith
  have htraceBound : eLpNorm (rootTraceObservable M Q old m m weights)
      (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (Inverse.orderTraceProfile M.gamma q
        (((m - Q.scale + 1 : ℤ) : ℝ))
        (|((m - Q.scale + 1 : ℤ) : ℝ)|)) := by
    simpa only [orderResetProfileConclusion, weights] using hprofile.1
  have hmeasReal : Measurable (fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)) := by
    have hr := root_trace_observable_measurable M Q old m m weights
    have hreal : (fun ω => traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)) =
        fun ω => rootTraceObservable M Q old m m weights ω - 4 := by
      funext ω
      rw [hroot ω]
      ring
    have hdef : Measurable (fun ω => traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)) :=
      hreal ▸ hr.sub_const 4
    exact hdef
  have htraceNonneg : ∀ ω, 0 ≤ traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ) :=
    fun ω => aoPerDepth_trace_nonneg M m Q ω
  have hnorm : eLpNorm (fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
      (ENNReal.ofReal q) μ ≤
      eLpNorm (rootTraceObservable M Q old m m weights)
        (ENNReal.ofReal q) μ := by
    apply eLpNorm_mono_ae hmeasReal.aestronglyMeasurable
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (htraceNonneg ω),
      Real.norm_eq_abs, abs_of_nonneg (hrootNonneg ω)]
    rw [hroot ω]
    linarith
  have htraceOfReal : eLpNorm (fun ω => ENNReal.ofReal
      (traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)))
      (ENNReal.ofReal q) μ =
      eLpNorm (fun ω => traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
        (ENNReal.ofReal q) μ := by
    change eLpNorm (ENNReal.ofReal ∘ fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
      (ENNReal.ofReal q) μ = _
    rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall htraceNonneg)]
  rw [htraceOfReal]
  exact hnorm.trans htraceBound

/-- The reset profile controls the finite spatial maximum with its exact
population payment. This is the high-order input to AO-PER-DEPTH. -/
theorem aoPerDepth_max_reset_profile
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (m : ℤ) (q : ℝ) (hq : 2 ≤ q) (t : ℕ) :
    eLpNorm (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) *
        ENNReal.ofReal (Inverse.orderTraceProfile M.gamma q
          ((t : ℝ) + 1) ((t : ℝ) + 1)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := originCube 2 m
  let cells := descendantsAtScale R (R.scale - (t : ℤ))
  have hscale : R.scale - (t : ℤ) ≤ R.scale := by
    exact sub_le_self _ (by exact_mod_cast (Nat.zero_le t))
  have hcells : cells.Nonempty := descendantsAtScale_nonempty R hscale
  let f : ↥cells → Cutoff.CutoffSample 2 → ℝ≥0∞ := fun Q ω =>
    ENNReal.ofReal (traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
  have hf : ∀ Q, Measurable (f Q) := by
    intro Q
    dsimp [f]
    let old := protectedOldLabel m (orderBand q)
    have hprofile := root_trace_observable_measurable M Q.1
      old m m
      (aoCirStepWeights m 1)
    have heq : (fun ω => traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)) =
      fun ω => rootTraceObservable M Q.1
        old m m
        (aoCirStepWeights m 1) ω - 4 := by
      funext ω
      have hOld : old < m := by
        dsimp [old, protectedOldLabel]
        omega
      have hcoeff : attenuatedCoefficient M
          old m
          (aoCirStepWeights m 1) ω = Cutoff.coefficientCutoff M.nu m ω := by
        ext x i j
        rw [aoCir_step_coefficient M old m hOld 1 ω x]
        have hentry := congrArg (fun a : RegCoeffField 2 => a.toFun x i j)
          (Main.mainInsertion_coefficient_one M (m - 1) ω)
        simpa only [show m - 1 + 1 = m by omega] using hentry
      rw [root_trace_observable_eq_trace_defect, hcoeff]
      ring
    have hdef : Measurable (fun ω => traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)) :=
      heq ▸ hprofile.sub_const 4
    exact ENNReal.continuous_ofReal.measurable.comp hdef
  have hB : ∀ Q : ↥cells,
      eLpNorm (f Q) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (Inverse.orderTraceProfile M.gamma q
          ((t : ℝ) + 1) ((t : ℝ) + 1)) := by
    intro Q
    have hQprop : Q.1 ∈ descendantsAtScale R (R.scale - (t : ℤ)) := by
      simpa only [cells] using Q.2
    rw [descendantsAtScale_eq_descendantsAtDepth R hscale] at hQprop
    have hdepth : R.scale - (R.scale - (t : ℤ)) = (t : ℤ) := by omega
    rw [hdepth] at hQprop
    have hQ' : Q.1 ∈ descendantsAtDepth R t := by
      simpa only [Int.toNat_natCast] using hQprop
    have hQscale : Q.1.scale = m - (t : ℤ) := by
      have hs := scale_eq_sub_of_mem_descendantsAtDepth hQ'
      simpa [R, originCube] using hs
    have hQN : Q.1.scale ≤ m := by rw [hQscale]; omega
    have hcell := aoPerDepth_cell_reset_profile reset M h hM hγ hstate Q.1 m hQN q hq
    have hfGap : ((m - Q.1.scale + 1 : ℤ) : ℝ) = (t : ℝ) + 1 := by
      rw [hQscale]
      push_cast
      ring
    have hprofileEq : |((m - Q.1.scale + 1 : ℤ) : ℝ)| = (t : ℝ) + 1 := by
      rw [hfGap, abs_of_nonneg (by positivity)]
    simpa only [μ, f, hfGap, hprofileEq,
      abs_of_nonneg (show 0 ≤ (t : ℝ) + 1 by positivity)] using hcell
  have hmax := finite_maximum_Lp μ (Finset.univ : Finset ↥cells) f
    (fun Q => hf Q) q (by linarith) _ (by
      intro Q _
      exact hB Q)
  have hmaxReal (ω : Cutoff.CutoffSample 2) :
      historyFiniteMax (Finset.univ : Finset ↥cells) (fun Q (_ : Unit) => f Q ω) () =
        ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t) := by
    have hsup := bank_finite_max_ofReal cells hcells (fun Q =>
        traceDefect (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
    simpa [f, cutoffTraceDefectMaxAtDepth, cells, R] using hsup
  have hfun : (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t)) =
      fun ω => historyFiniteMax (Finset.univ : Finset ↥cells)
        (fun Q (_ : Unit) => f Q ω) () := by
    funext ω
    exact (hmaxReal ω).symm
  have hmaxFun :
      (fun ω => historyFiniteMax (Finset.univ : Finset ↥cells)
        (fun Q (_ : Unit) => f Q ω) ()) =
        historyFiniteMax (Finset.univ : Finset ↥cells) f := by
    funext ω
    rfl
  rw [hfun, hmaxFun]
  have hcard : (cells.card : ℝ≥0∞) ^ (1 / q : ℝ) =
      ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) := by
    have hcardR : (cells.card : ℝ) = 9 ^ t := by
      have hscale' : R.scale - (t : ℤ) ≤ R.scale := hscale
      dsimp [cells]
      rw [descendantsAtScale_eq_descendantsAtDepth R hscale']
      have hdepth : R.scale - (R.scale - (t : ℤ)) = (t : ℤ) := by omega
      rw [hdepth, descendantsAtDepth_card]
      norm_num
    have hpos : 0 < (cells.card : ℝ) := by rw [hcardR]; positivity
    have hroot : Real.rpow (cells.card : ℝ) (1 / q) =
        Real.rpow 9 ((t : ℝ) / q) := by
      rw [hcardR]
      calc
        Real.rpow ((9 : ℝ) ^ t) (1 / q) =
            Real.rpow 9 ((t : ℝ) * (1 / q)) := by
          exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 9)
            t (1 / q)).symm
        _ = Real.rpow 9 ((t : ℝ) / q) := by
          congr 1
          field_simp
    have hcast : (cells.card : ℝ≥0∞) = ENNReal.ofReal (cells.card : ℝ) := by norm_cast
    calc
      (cells.card : ℝ≥0∞) ^ (1 / q : ℝ) =
          ENNReal.ofReal (cells.card : ℝ) ^ (1 / q : ℝ) := by
        rw [hcast]
      _ = ENNReal.ofReal (Real.rpow (cells.card : ℝ) (1 / q)) :=
        ENNReal.ofReal_rpow_of_pos hpos
      _ = ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) := by
        exact congrArg ENNReal.ofReal hroot
  have hcard' : (((Finset.univ : Finset ↥cells).card : ℝ≥0∞) ^
      (1 / q : ℝ)) = ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hcard
  rw [hcard'] at hmax
  exact hmax

/-- A uniform bound on each descendant pays the exact finite-population
factor when passed to the depth maximum. -/
theorem aoPerDepth_max_from_cell_bound
    (M : ABKModel 2) (m : ℤ) (q A : ℝ) (t : ℕ)
    (hq : 0 < q)
    (hcell : ∀ Q : TriadicCube 2,
      Q ∈ descendantsAtDepth (originCube 2 m) t →
      eLpNorm (fun ω => ENNReal.ofReal
        (traceDefect (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu m ω).toFun
          (Annealed.sigmaBar M m : ℝ)))
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal A) :
    eLpNorm (fun ω => ENNReal.ofReal
      (cutoffTraceDefectMaxAtDepth M m ω t))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) * ENNReal.ofReal A := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R := originCube 2 m
  let cells := descendantsAtScale R (R.scale - (t : ℤ))
  have hscale : R.scale - (t : ℤ) ≤ R.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le t)
  have hcells : cells.Nonempty := descendantsAtScale_nonempty R hscale
  let f : ↥cells → Cutoff.CutoffSample 2 → ℝ≥0∞ := fun Q ω =>
    ENNReal.ofReal (traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
  have hf : ∀ Q, Measurable (f Q) := by
    intro Q
    change Measurable (fun ω => ENNReal.ofReal
      (Cold.coldNativeCellTrace M m Q.1 ω))
    exact ENNReal.continuous_ofReal.measurable.comp
      (Cold.coldNativeCellTrace_measurable M m Q.1)
  have hB : ∀ Q : ↥cells,
      eLpNorm (f Q) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal A := by
    intro Q
    have hQprop : Q.1 ∈ descendantsAtScale R (R.scale - (t : ℤ)) := by
      simpa only [cells] using Q.2
    rw [descendantsAtScale_eq_descendantsAtDepth R hscale] at hQprop
    have hdepth : R.scale - (R.scale - (t : ℤ)) = (t : ℤ) := by omega
    rw [hdepth] at hQprop
    have hQdepth : Q.1 ∈ descendantsAtDepth R t := by
      simpa only [Int.toNat_natCast] using hQprop
    simpa only [f, μ, R] using hcell Q.1 hQdepth
  have hmax := finite_maximum_Lp μ (Finset.univ : Finset ↥cells) f
    hf q hq _ (by intro Q _; exact hB Q)
  have hmaxReal (ω : Cutoff.CutoffSample 2) :
      historyFiniteMax (Finset.univ : Finset ↥cells)
        (fun Q (_ : Unit) => f Q ω) () =
        ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t) := by
    have hsup := bank_finite_max_ofReal cells hcells (fun Q =>
      traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ))
    simpa [f, cutoffTraceDefectMaxAtDepth, cells, R] using hsup
  have hfun : (fun ω => ENNReal.ofReal (cutoffTraceDefectMaxAtDepth M m ω t)) =
      fun ω => historyFiniteMax (Finset.univ : Finset ↥cells)
        (fun Q (_ : Unit) => f Q ω) () := by
    funext ω
    exact (hmaxReal ω).symm
  have hmaxFun : (fun ω => historyFiniteMax (Finset.univ : Finset ↥cells)
        (fun Q (_ : Unit) => f Q ω) ()) =
      historyFiniteMax (Finset.univ : Finset ↥cells) f := by
    funext ω
    rfl
  rw [hfun, hmaxFun]
  have hcardR : (cells.card : ℝ) = 9 ^ t := by
    dsimp [cells]
    rw [descendantsAtScale_eq_descendantsAtDepth R hscale]
    have hdepth : R.scale - (R.scale - (t : ℤ)) = (t : ℤ) := by omega
    rw [hdepth, descendantsAtDepth_card]
    norm_num
  have hcard : (cells.card : ℝ≥0∞) ^ (1 / q : ℝ) =
      ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) := by
    have hpos : 0 < (cells.card : ℝ) := by rw [hcardR]; positivity
    have hroot : Real.rpow (cells.card : ℝ) (1 / q) =
        Real.rpow 9 ((t : ℝ) / q) := by
      rw [hcardR]
      calc
        Real.rpow ((9 : ℝ) ^ t) (1 / q) =
            Real.rpow 9 ((t : ℝ) * (1 / q)) := by
          exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 9)
            t (1 / q)).symm
        _ = Real.rpow 9 ((t : ℝ) / q) := by
          congr 1
          field_simp
    have hcast : (cells.card : ℝ≥0∞) = ENNReal.ofReal (cells.card : ℝ) := by norm_cast
    calc
      (cells.card : ℝ≥0∞) ^ (1 / q : ℝ) =
          ENNReal.ofReal (cells.card : ℝ) ^ (1 / q : ℝ) := by rw [hcast]
      _ = ENNReal.ofReal (Real.rpow (cells.card : ℝ) (1 / q)) :=
        ENNReal.ofReal_rpow_of_pos hpos
      _ = ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) := congrArg ENNReal.ofReal hroot
  have hcard' : (((Finset.univ : Finset ↥cells).card : ℝ≥0∞) ^
      (1 / q : ℝ)) = ENNReal.ofReal (Real.rpow 9 ((t : ℝ) / q)) := by
    simpa only [Finset.card_univ, Fintype.card_coe] using hcard
  rw [hcard'] at hmax
  exact hmax

private theorem aoPerDepth_height_bound {q : ℝ} (hq : 2 ≤ q) :
    (Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 ≤
      397 + 12 * (Real.log q / Real.log 3) := by
  let k := Inverse.orderBand q
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hheight : (Inverse.heightEntrance k : ℝ) + 20 =
      397 + 12 * (k : ℝ) := by
    norm_num [Inverse.heightEntrance]
    ring
  have hk : (k : ℝ) ≤ Real.log q / Real.log 3 := by
    by_cases hq64 : q ≤ 64
    · have hdiv : q / 64 ≤ 1 :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).2 (by simpa using hq64)
      have hmax : max 1 (q / 64) = 1 := max_eq_left hdiv
      have hk0 : k = 0 := by
        dsimp [k, Inverse.orderBand]
        rw [hmax]
        simp
      rw [hk0]
      have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith [hq])
      simpa using div_nonneg hlogq hlog3.le
    · have h64q : 64 < q := lt_of_not_ge hq64
      have hdiv : 1 < q / 64 :=
        (lt_div_iff₀ (by norm_num : (0 : ℝ) < 64)).2 (by simpa using h64q)
      have hmax : max 1 (q / 64) = q / 64 := max_eq_right hdiv.le
      have harg : 0 ≤ Real.log (q / 64) / Real.log 3 :=
        div_nonneg (Real.log_nonneg hdiv.le) hlog3.le
      have hceil : (k : ℝ) < Real.log (q / 64) / Real.log 3 + 1 := by
        dsimp [k, Inverse.orderBand]
        rw [hmax]
        exact Nat.ceil_lt_add_one harg
      have hlog64 : Real.log 3 < Real.log 64 :=
        Real.log_lt_log (by norm_num) (by norm_num)
      have hratio : 1 < Real.log 64 / Real.log 3 := by
        exact (lt_div_iff₀ hlog3).2 (by simpa only [one_mul] using hlog64)
      have hlogEq : Real.log q = Real.log (q / 64) + Real.log 64 := by
        have hmul : (q / 64) * 64 = q := by field_simp
        have hqdivpos : 0 < q / 64 := lt_trans (by norm_num) hdiv
        calc
          Real.log q = Real.log ((q / 64) * 64) := by
            exact congrArg Real.log hmul.symm
          _ = Real.log (q / 64) + Real.log 64 :=
            Real.log_mul (ne_of_gt hqdivpos) (by norm_num : (64 : ℝ) ≠ 0)
      rw [hlogEq]
      have hratio' :
          Real.log (q / 64) / Real.log 3 + 1 <
            Real.log (q / 64) / Real.log 3 + Real.log 64 / Real.log 3 := by
        linarith
      have htarget :
          Real.log (q / 64) / Real.log 3 + Real.log 64 / Real.log 3 =
            (Real.log (q / 64) + Real.log 64) / Real.log 3 := by
        field_simp [ne_of_gt hlog3]
      rw [← htarget]
      exact hceil.le.trans (le_of_lt hratio')
  rw [hheight]
  nlinarith [mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 12)]

private theorem aoPerDepth_height_power_bound {γ q : ℝ}
    (hγ : γ ≤ 17 / 50000) (hγ0 : 0 ≤ γ) (hq : 2 ≤ q) :
    (3 : ℝ) ^ (4 * γ *
      ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20)) ≤
      2 * q ^ (48 * γ) := by
  have hheight := aoPerDepth_height_bound hq
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : 0 < q := by linarith
  have hexp : 4 * γ * ((Inverse.heightEntrance
      (Inverse.orderBand q) : ℝ) + 20) ≤
      4 * γ * (397 + 12 * (Real.log q / Real.log 3)) := by
    exact mul_le_mul_of_nonneg_left hheight (by positivity)
  have hmainExp : 4 * γ * 397 ≤ (14 / 25 : ℝ) := by
    nlinarith [hγ]
  have hmain : (3 : ℝ) ^ (4 * γ * 397) ≤ (3 : ℝ) ^ (14 / 25 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) hmainExp
  have hpow : ((3 : ℝ) ^ (14 / 25 : ℝ)) ^ 25 = (3 : ℝ) ^ 14 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hbase : (3 : ℝ) ^ (14 / 25 : ℝ) < 2 := by
    apply lt_of_pow_lt_pow_left₀ 25 (by positivity)
    calc
      ((3 : ℝ) ^ (14 / 25 : ℝ)) ^ 25 = (3 : ℝ) ^ 14 := hpow
      _ < (2 : ℝ) ^ 25 := by norm_num
  have hheightPow : (3 : ℝ) ^
      (4 * γ * ((Inverse.heightEntrance
        (Inverse.orderBand q) : ℝ) + 20)) ≤
      (3 : ℝ) ^ (4 * γ * 397 +
        48 * γ * (Real.log q / Real.log 3)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ))
      (by nlinarith [hexp])
  have hlogIdentity : (3 : ℝ) ^
      (48 * γ * (Real.log q / Real.log 3)) = q ^ (48 * γ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
      Real.rpow_def_of_pos hqpos]
    congr 1
    field_simp [ne_of_gt hlog3]
  calc
    _ ≤ (3 : ℝ) ^ (4 * γ * 397 +
          48 * γ * (Real.log q / Real.log 3)) := hheightPow
    _ = (3 : ℝ) ^ (4 * γ * 397) *
          (3 : ℝ) ^ (48 * γ * (Real.log q / Real.log 3)) :=
        Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _
    _ ≤ 2 * q ^ (48 * γ) := by
      rw [hlogIdentity]
      exact mul_le_mul_of_nonneg_right (hmain.trans_lt hbase).le
        (Real.rpow_nonneg (le_of_lt hqpos) _)

theorem aoPerDepth_raw_envelope {γ q : ℝ} {t : ℕ}
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ 17 / 50000) (hq : 20 ≤ q) :
    Inverse.orderTraceProfile γ q ((t : ℝ) + 1) ((t : ℝ) + 1) ≤
      (16 + 22480 * γ * q * ((t : ℝ) + 22)) *
        q ^ (64 * γ) * (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) := by
  have hq2 : 2 ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hheight := aoPerDepth_height_power_bound hγ hγ0 hq2
  have hheight20 :
      (Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 ≤ 20 * q := by
    by_cases hq64 : q ≤ 64
    · have hk : Inverse.orderBand q = 0 := by
        dsimp [Inverse.orderBand]
        have hdiv : q / 64 ≤ 1 :=
          (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).2 (by simpa using hq64)
        rw [max_eq_left hdiv]
        simp
      rw [hk]
      norm_num [Inverse.heightEntrance]
      nlinarith
    · have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
      have hlog3One : 1 < Real.log 3 := by
        exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
          Real.exp_one_lt_three
      have hlogq : Real.log q ≤ q := by
        have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < q)
        linarith
      have hlogratio : Real.log q / Real.log 3 ≤ q := by
        apply (div_le_iff₀ hlog3).2
        nlinarith
      have hheightBound := aoPerDepth_height_bound hq2
      have hq50 : 50 ≤ q := by
        have h64 : 64 < q := lt_of_not_ge hq64
        linarith
      calc
        _ ≤ 397 + 12 * (Real.log q / Real.log 3) := hheightBound
        _ ≤ 397 + 12 * q := by nlinarith [hlogratio]
        _ ≤ 20 * q := by nlinarith
  have hcoeff :
      4 * (2 + 2810 * γ *
          ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 +
            q * (((t : ℝ) + 1) + 1))) ≤
        4 * (2 + 2810 * γ * q * ((t : ℝ) + 22)) := by
    have hterm := add_le_add_right hheight20 (q * (((t : ℝ) + 1) + 1))
    have hmul := mul_le_mul_of_nonneg_left hterm hγ0
    nlinarith [hmul]
  have hcoeff0 : 0 ≤ 4 *
      (2 + 2810 * γ * (q * ((t : ℝ) + 22))) := by positivity
  have hqpow : q ^ (48 * γ) ≤ q ^ (64 * γ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ q)
    nlinarith [hγ0]
  have hcoeffPow :
      4 * (2 + 2810 * γ *
          ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 +
            q * (((t : ℝ) + 1) + 1))) * 2 * q ^ (48 * γ) ≤
        (16 + 22480 * γ * q * ((t : ℝ) + 22)) * q ^ (64 * γ) := by
    have hleft : 4 * (2 + 2810 * γ *
        ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 +
          q * (((t : ℝ) + 1) + 1))) * 2 ≤
        16 + 22480 * γ * q * ((t : ℝ) + 22) := by
      nlinarith [hcoeff]
    have hpow0 : 0 ≤ q ^ (48 * γ) := Real.rpow_nonneg (le_of_lt hqpos) _
    have htarget0 : 0 ≤ 16 + 22480 * γ * q * ((t : ℝ) + 22) := by positivity
    calc
      _ ≤ (16 + 22480 * γ * q * ((t : ℝ) + 22)) * q ^ (48 * γ) :=
        mul_le_mul_of_nonneg_right hleft hpow0
      _ ≤ (16 + 22480 * γ * q * ((t : ℝ) + 22)) * q ^ (64 * γ) :=
        mul_le_mul_of_nonneg_left hqpow htarget0
  unfold Inverse.orderTraceProfile
  have hfactor :
      (3 : ℝ) ^ (4 * γ *
          ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20) +
        2 * γ * ((t : ℝ) + 1) + 2 * γ * ((t : ℝ) + 1)) =
        (3 : ℝ) ^ (4 * γ *
          ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20)) *
        (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hfactor]
  calc
    _ ≤ (4 * (2 + 2810 * γ *
          ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 +
            q * (((t : ℝ) + 1) + 1))) * 2 * q ^ (48 * γ)) *
        (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) := by
      let A := 4 * (2 + 2810 * γ *
        ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20 +
          q * (((t : ℝ) + 1) + 1)))
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hD : 0 ≤ (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1)) :=
        Real.rpow_nonneg (by norm_num) _
      calc
        _ = A * ((3 : ℝ) ^ (4 * γ *
              ((Inverse.heightEntrance (Inverse.orderBand q) : ℝ) + 20)) *
              (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1))) := by dsimp [A]
        _ ≤ A * ((2 * q ^ (48 * γ)) *
              (3 : ℝ) ^ (4 * γ * ((t : ℝ) + 1))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hheight hD) hA
        _ = _ := by dsimp [A]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoeffPow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)

/-- The finite-even node gives the sharper native-order input needed before
paying the spatial maximum. The even ceiling costs at most two orders above
12, while orders below 12 use the order-12 cap. -/
theorem aoPerDepth_native_cap
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (m : ℤ) {q : ℝ} (hq : 1 ≤ q)
    (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ)) :
    MemLp (cutoffTraceDefect M m m) (ENNReal.ofReal q)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (cutoffTraceDefect M m m) (ENNReal.ofReal q)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
        900000 * M.gamma * (if q < 12 then 12 else q + 2) := by
  let P := smallGammaSeedP M.gamma
  let r := aoCirEvenCeiling q
  have hP20 : 20 ≤ P := by dsimp [P, smallGammaSeedP]; omega
  have hPeven : Even P := by
    dsimp [P, smallGammaSeedP]
    by_cases hf : 20 ≤ 2 * ⌊(1 / 16384 : ℝ) / (2 * M.gamma)⌋₊
    · rw [max_eq_right hf]
      exact even_two_mul _
    · have hle : 2 * ⌊(1 / 16384 : ℝ) / (2 * M.gamma)⌋₊ ≤ 20 := by omega
      rw [max_eq_left hle]
      exact ⟨10, rfl⟩
  have hPcast : (P : ℝ) = (smallGammaSeedP M.gamma : ℝ) := by rfl
  have hr12 : 12 ≤ r := by
    dsimp [r, aoCirEvenCeiling]
    have h6real : (6 : ℝ) ≤
        (Nat.ceil (max 6 (q / 2)) : ℝ) :=
      (le_max_left (6 : ℝ) (q / 2)).trans (Nat.le_ceil _)
    have h6 : 6 ≤ Nat.ceil (max 6 (q / 2)) := by exact_mod_cast h6real
    omega
  have hrEven : Even r := by
    dsimp [r, aoCirEvenCeiling]
    exact even_two_mul _
  have hqHalf : max (6 : ℝ) (q / 2) ≤ (P : ℝ) / 2 := by
    apply max_le
    · have hPreal : (20 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP20
      linarith
    · rw [hPcast]
      linarith
  have hrP : r ≤ P := by
    dsimp [r, aoCirEvenCeiling]
    obtain ⟨k, hk⟩ := hPeven
    have hkCast : (P : ℝ) / 2 = (k : ℝ) := by rw [hk]; norm_num
    have hceil : Nat.ceil (max 6 (q / 2)) ≤ k := by
      rw [Nat.ceil_le]
      rw [hkCast] at hqHalf
      exact hqHalf
    rw [hk]
    omega
  have hqR : q ≤ (r : ℝ) := by
    have hq0 : 0 ≤ q := le_trans (by norm_num : (0 : ℝ) ≤ 1) hq
    have hmax : q / 2 ≤ max (6 : ℝ) (q / 2) := le_max_right _ _
    have hceil : q / 2 ≤ (Nat.ceil (max 6 (q / 2)) : ℝ) :=
      hmax.trans (Nat.le_ceil _)
    dsimp [r, aoCirEvenCeiling]
    push_cast
    nlinarith [hceil, hq0]
  have hrBound : (r : ℝ) ≤ if q < 12 then 12 else q + 2 := by
    by_cases hq12 : q < 12
    · have hmax : max (6 : ℝ) (q / 2) = 6 := max_eq_left (by linarith)
      simp [r, aoCirEvenCeiling, hmax, hq12]
    · have hmax : max (6 : ℝ) (q / 2) = q / 2 :=
        max_eq_right (by linarith)
      have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ max (6 : ℝ) (q / 2))
      dsimp [r, aoCirEvenCeiling]
      rw [hmax] at hceil ⊢
      simp only [hq12] at hceil ⊢
      push_cast
      nlinarith
  have hfinite := (ao_cir_finite_even M h hM hγ m hstate).1
  have hcap := hfinite r hr12 hrEven hrP
  have hExp : ENNReal.ofReal q ≤ (r : ℝ≥0∞) := by
    calc
      ENNReal.ofReal q ≤ ENNReal.ofReal (r : ℝ) := ENNReal.ofReal_le_ofReal hqR
      _ = (r : ℝ≥0∞) := by norm_cast
  have hmem := hcap.1.mono_exponent hExp
  have hnorm : lpNorm (cutoffTraceDefect M m m) (ENNReal.ofReal q)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm (cutoffTraceDefect M m m) (r : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    unfold lpNorm
    exact ENNReal.toReal_mono hcap.1.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hExp)
  refine ⟨hmem, ?_⟩
  calc
    _ ≤ 900000 * M.gamma * (r : ℝ) := hnorm.trans hcap.2
    _ ≤ 900000 * M.gamma * (if q < 12 then 12 else q + 2) :=
      mul_le_mul_of_nonneg_left hrBound
        (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)

/-- At a fixed cutoff and arbitrary deterministic frame, a translated cell
trace has the same law as the origin cell at its scale. -/
private theorem aoPerDepth_cell_trace_measurable_at_frame
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (σ : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun σ) := by
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu m
  have hX : Measurable X := by simpa [X] using Cutoff.measurable_coefficientCutoff M.nu m
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) := by
    intro ω
    simpa [X] using Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M m ω
  have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet hX hEll Q
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet hX hEll Q
  have hTraceUL : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
  have hTraceLR : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
  change Measurable (fun ω =>
    σ⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft +
      σ * Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight - 4)
  exact (hTraceUL.const_mul _).add (hTraceLR.const_mul _)
    |>.sub_const 4

private theorem aoPerDepth_cell_trace_identDistrib_at_frame
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (σ : ℝ) :
    ProbabilityTheory.IdentDistrib
      (fun ω : Cutoff.CutoffSample 2 =>
        traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun σ)
      (fun ω : Cutoff.CutoffSample 2 =>
        traceDefect (cubeSet (originCube 2 Q.scale))
          (Cutoff.coefficientCutoff M.nu m ω).toFun σ)
      (Cutoff.cutoffSampleLaw M).toMeasure
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let fQ : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun σ
  let fO : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 Q.scale))
      (Cutoff.coefficientCutoff M.nu m ω).toFun σ
  have hmap (R : TriadicCube 2) :
      Measure.map (fun ω : Cutoff.CutoffSample 2 =>
        traceDefect (cubeSet R) (Cutoff.coefficientCutoff M.nu m ω).toFun σ) μ =
      Measure.map (fun a : RegCoeffField 2 => traceDefect (cubeSet R) a.toFun σ)
        (Cutoff.coefficientCutoffLaw M m) := by
    have hm := Model.aemeasurable_traceDefect_cutoffLaw M m R σ
    rw [Cutoff.coefficientCutoffLaw_eq_map] at hm ⊢
    rw [AEMeasurable.map_map_of_aemeasurable hm
      (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable]
    rfl
  refine ⟨(aoPerDepth_cell_trace_measurable_at_frame M m Q σ).aemeasurable,
    (aoPerDepth_cell_trace_measurable_at_frame M m (originCube 2 Q.scale) σ).aemeasurable,
    ?_⟩
  change Measure.map fQ μ = Measure.map fO μ
  rw [hmap Q, hmap (originCube 2 Q.scale)]
  exact Model.map_traceDefect_cube_eq_origin M m Q σ

/-- The finite-even root cap transfers to any translated cell at the same
scale, and remains an `ENNReal` bound after applying `ofReal`. -/
theorem aoPerDepth_native_cell_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    (m : ℤ) (Q : TriadicCube 2) (hQ : Q.scale = m)
    {q : ℝ} (hq : 1 ≤ q) (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ)) :
    eLpNorm (fun ω => ENNReal.ofReal
      (traceDefect (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (900000 * M.gamma * (if q < 12 then 12 else q + 2)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let fQ : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ)
  let fO : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 Q.scale))
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M m : ℝ)
  have hnative := aoPerDepth_native_cap M h hM hγ hstate m hq hqP
  have hID := aoPerDepth_cell_trace_identDistrib_at_frame M m Q
    (Annealed.sigmaBar M m : ℝ)
  have hrootMem : MemLp fO (ENNReal.ofReal q) μ := by
    have hEq : fO = cutoffTraceDefect M m m := by
      funext ω
      simp only [fO, cutoffTraceDefect, hQ]
    rw [hEq]
    exact hnative.1
  have hrootNorm : lpNorm fO (ENNReal.ofReal q) μ ≤
      900000 * M.gamma * (if q < 12 then 12 else q + 2) := by
    have hEq : fO = cutoffTraceDefect M m m := by
      funext ω
      simp only [fO, cutoffTraceDefect, hQ]
    rw [hEq]
    exact hnative.2
  have hcellMem : MemLp fQ (ENNReal.ofReal q) μ :=
    hID.memLp_iff.mpr hrootMem
  have hcellNormEq : lpNorm fQ (ENNReal.ofReal q) μ =
      lpNorm fO (ENNReal.ofReal q) μ := by
    unfold lpNorm
    exact congrArg ENNReal.toReal (hID.eLpNorm_eq (p := ENNReal.ofReal q))
  have hcellNonneg : ∀ ω, 0 ≤ fQ ω := by
    intro ω
    obtain ⟨Λ, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
    exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos
      hEll (Annealed.sigmaBar_characterization M m).1
  have hreal : eLpNorm fQ (ENNReal.ofReal q) μ =
      ENNReal.ofReal (lpNorm fQ (ENNReal.ofReal q) μ) := by
    have htoReal : (eLpNorm fQ (ENNReal.ofReal q) μ).toReal =
        lpNorm fQ (ENNReal.ofReal q) μ := toReal_eLpNorm
    rw [← htoReal]
    exact (ENNReal.ofReal_toReal hcellMem.eLpNorm_ne_top).symm
  change eLpNorm (ENNReal.ofReal ∘ fQ) (ENNReal.ofReal q) μ ≤ _
  rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall hcellNonneg), hreal]
  exact ENNReal.ofReal_le_ofReal (hcellNormEq.trans_le hrootNorm)

private theorem aoPerDepth_descendant_closure_subset {Q : TriadicCube 2} {r : ℕ}
    {R : TriadicCube 2} (hQ : Q ∈ descendantsAtDepth R r) :
    closure (openCubeSet Q) ⊆ closure (cubeSet R) := by
  exact closure_mono ((openCubeSet_subset_of_mem_descendantsAtDepth hQ).trans
    (openCubeSet_subset_cubeSet R))

private theorem aoPerDepth_parent_closure_inside_next_open (m : ℤ) :
    closure (cubeSet (originCube 2 m)) ⊆ openCubeSet (originCube 2 (m + 1)) := by
  rw [Algsuperdiff.Section3.Provider.Whitney.closure_cubeSet_eq_closedBall]
  rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
  have hscale : (3 : ℝ) ^ (m + 1) = (3 : ℝ) ^ m * 3 := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) m 1]
    norm_num
  have hrad : Homogenization.cubeRadius (originCube 2 m) <
      Homogenization.cubeRadius (originCube 2 (m + 1)) := by
    simp only [Homogenization.cubeRadius,
      Homogenization.cubeScaleFactor_originCube]
    rw [hscale]
    have hp : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
    nlinarith
  have hcenter : Homogenization.cubeCenter (originCube 2 m) =
      Homogenization.cubeCenter (originCube 2 (m + 1)) := by
    ext i
    simp [Homogenization.cubeCenter, originCube]
  rw [hcenter]
  exact Metric.closedBall_subset_ball hrad

private theorem aoPerDepth_step_trace_eq_partial
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (base N frameLabel : ℤ) (hbase : base < N) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    Gaussian.squareTrace Q M.nu (Annealed.sigmaBar M frameLabel)
        (cirSquareRestrictionCLM Q hQ
          (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) t ω)) =
      traceDefect (cubeSet Q) (Model.partialInsertedCoefficient M (N - 1) t ω).toFun
        (Annealed.sigmaBar M frameLabel : ℝ) := by
  have hreset := aoCir_step_trace_eq_squareTrace M Q n ell hQ hK
    base N frameLabel hbase t ω
  have htrace := Inverse.root_trace_observable_eq_trace_defect M Q base N
    frameLabel (aoCirStepWeights N t) ω
  have hcoeff : attenuatedCoefficient M base N (aoCirStepWeights N t) ω =
      Model.partialInsertedCoefficient M (N - 1) t ω := by
    funext x
    exact aoCir_step_coefficient M base N hbase t ω x
  rw [hcoeff] at htrace
  linarith

private theorem aoPerDepth_partialInserted_zero (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M n 0 ω = Cutoff.coefficientCutoff M.nu n ω := by
  ext x i j
  simp [Model.partialInsertedCoefficient]

private theorem aoPerDepth_partialInserted_one (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M n 1 ω = Cutoff.coefficientCutoff M.nu (n + 1) ω := by
  exact Main.mainInsertion_coefficient_one M n ω

private theorem aoPerDepth_direct_old_frame_cell_norm
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ j : ℤ, nativeInductionState M h j)
    (m : ℤ) (Q : TriadicCube 2) (t : ℕ)
    (htpos : 0 < t)
    (hQdepth : Q ∈ descendantsAtDepth (originCube 2 m) t)
    {q : ℝ} (hq12 : 12 ≤ q) (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ))
    (hwindow : M.gamma * q * ((t : ℝ) + 2) ≤ 1 / 512) :
    MemLp (fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M (m - (t : ℤ)) : ℝ))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M (m - (t : ℤ)) : ℝ))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      900000 * M.gamma * (q + 2) +
        (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) := by
  classical
  let k : ℤ := m - (t : ℤ)
  let R : TriadicCube 2 := originCube 2 m
  let s : Finset Unit := Finset.univ
  let w : Unit → ℝ := fun _ => 1
  let Qs : Unit → TriadicCube 2 := fun _ => Q
  let hQ : ∀ a, closure (openCubeSet (Qs a)) ⊆ closure (cubeSet R) := by
    intro a
    exact aoPerDepth_descendant_closure_subset hQdepth
  let hK : closure (cubeSet R) ⊆ openCubeSet (originCube 2 (m + 1)) := by
    exact aoPerDepth_parent_closure_inside_next_open m
  have hQscale : Q.scale = k := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hQdepth
    simpa [R, k, originCube] using hs
  have htk : k < m := by
    dsimp [k]
    have htcast : 0 < (t : ℤ) := by exact_mod_cast htpos
    omega
  have hw : ∀ a ∈ s, 0 ≤ w a := by intro a ha; simp [w]
  have hsum : ∑ a ∈ s, w a = 1 := by simp [s, w]
  have hscale : ∀ a ∈ s, (Qs a).scale = k := by
    intro a ha
    simpa [Qs] using hQscale
  let FamilyAt := aoCirFiniteEvenFamilyAt s w Qs M h m k hQ hw hsum
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let fK : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M k : ℝ)
  have htrace (j : ℤ) (τ : ℝ) (ω : Cutoff.CutoffSample 2) :
      cirFamilyTrace (FamilyAt j) τ ω =
        Gaussian.squareTrace Q M.nu (Annealed.sigmaBar M k)
          (cirSquareRestrictionCLM Q (hQ ())
            (modelInsertedScalar (closure (cubeSet R)) (j - 1) τ ω)) := by
    have h := aoCirFiniteEvenFamilyAt_trace s w Qs M h m k hQ hw hsum j τ ω
    simpa [FamilyAt, s, w, Qs] using h
  have hbaseEq :
      (fun ω => cirFamilyTrace (FamilyAt (k + 1)) 0 ω) =
        Cold.coldNativeCellTrace M k Q := by
    funext ω
    rw [htrace]
    have hstep := aoPerDepth_step_trace_eq_partial M Q m (m + 1) (hQ ()) hK
      k (k + 1) k (by omega) 0 ω
    have hzero := aoPerDepth_partialInserted_zero M k ω
    simpa only [show k + 1 - 1 = k by omega, hzero,
      Cold.coldNativeCellTrace] using hstep
  have hfinalEq : (fun ω => cirFamilyTrace (FamilyAt m) 1 ω) = fK := by
    funext ω
    rw [htrace]
    rw [aoPerDepth_step_trace_eq_partial M Q m (m + 1) (hQ ()) hK
      k m k htk 1 ω]
    have hone := aoPerDepth_partialInserted_one M (m - 1) ω
    have hindex : m - 1 + 1 = m := by omega
    rw [show Model.partialInsertedCoefficient M (m - 1) 1 ω =
      Cutoff.coefficientCutoff M.nu m ω by simpa only [hindex] using hone]
  have hfamilyMem (N : ℤ) (hN : k ≤ N) (τ : ℝ)
      (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
      MemLp (cirFamilyTrace (FamilyAt N) τ) (ENNReal.ofReal q) μ := by
    have hmem := aoCir_reset_square_family_memLp reset M h hM hγ hγsmall
      hstate s w Qs m (m + 1) k N hQ hK hscale hN hw hsum
      (q3ModelAmplitude M h N) (q3ModelLength N) q (by linarith [hq12])
      τ hτ0 hτ1
    simpa only [FamilyAt, aoCirFiniteEvenFamilyAt, μ] using hmem.1
  have hbaseMem : MemLp (Cold.coldNativeCellTrace M k Q)
      (ENNReal.ofReal q) μ := by
    apply (Cold.coldNativeCellTrace_memLp_iff M k Q
      (ENNReal.ofReal q)).2
    simpa only [hQscale, μ] using
      (aoPerDepth_native_cap M h hM hγ hstate k (q := q) (by linarith [hq12])
        (by simpa only [k] using hqP)).1
  have hbaseNorm : lpNorm (Cold.coldNativeCellTrace M k Q)
      (ENNReal.ofReal q) μ ≤ 900000 * M.gamma * (q + 2) := by
    rw [Cold.coldNativeCellTrace_norm]
    have hnative := aoPerDepth_native_cap M h hM hγ hstate k (q := q)
      (by linarith [hq12]) (by simpa only [k] using hqP)
    have hq12' : ¬ q < 12 := by linarith
    simpa [hQscale, μ, hq12'] using hnative.2
  let A : ℕ → ℝ := fun i => Gaussian.positiveLpNorm μ q
    (cirFamilyTrace (FamilyAt (k + (i : ℤ) + 1)) 0)
  have hA0 : A 0 = lpNorm (Cold.coldNativeCellTrace M k Q)
      (ENNReal.ofReal q) μ := by
    simp only [A, Nat.cast_zero, Int.add_zero]
    have hnorm := Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ
      (by linarith [hq12]) (cirFamilyTrace (FamilyAt (k + 1)) 0)
      (cirFamilyTrace_nonneg (FamilyAt (k + 1)) 0)
      (hfamilyMem (k + 1) (by omega) 0 (by norm_num) (by norm_num))
    rw [hnorm, ← hbaseEq]
    rfl
  have hfinalNorm : Gaussian.positiveLpNorm μ q
      (cirFamilyTrace (FamilyAt m) 1) = lpNorm fK (ENNReal.ofReal q) μ := by
    have hnorm := Gaussian.positiveLpNorm_eq_eLpNorm_toReal μ
      (by linarith [hq12]) (cirFamilyTrace (FamilyAt m) 1)
      (cirFamilyTrace_nonneg (FamilyAt m) 1)
      (hfamilyMem m (by omega) 1 (by norm_num) (by norm_num))
    rw [hnorm, ← hfinalEq]
    rfl
  have hendpoint (N : ℤ) :
      cirFamilyTrace (FamilyAt N) 1 = cirFamilyTrace (FamilyAt (N + 1)) 0 := by
    have htraceSum (j : ℤ) (τ : ℝ) (ω : Cutoff.CutoffSample 2) :
        cirFamilyTrace (FamilyAt j) τ ω =
          ∑ a ∈ s, w a * Gaussian.squareTrace (Qs a) M.nu
            (Annealed.sigmaBar M k)
            (cirSquareRestrictionCLM (Qs a) (hQ a)
              (modelInsertedScalar (closure (cubeSet R)) (j - 1) τ ω)) := by
      simpa [s, w, Qs] using htrace j τ ω
    exact aoCir_finite_even_family_succ_endpoint FamilyAt s w Qs M h m
      (m + 1) k N hQ hK hw hsum htraceSum
  have hstep (i : ℕ) (hi : i < t) : A (i + 1) - A i ≤
      19 * q * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120) := by
    let N : ℤ := k + (i : ℤ) + 1
    have hN : k + 1 ≤ N := by dsimp [N]; omega
    have hNhi : N ≤ m := by
      have hiSucc : (i : ℤ) + 1 ≤ (t : ℤ) := by
        exact_mod_cast Nat.succ_le_of_lt hi
      dsimp [N, k]
      omega
    have hNdiff : N - k = (i : ℤ) + 1 := by
      dsimp [N]
      omega
    have hwin : M.gamma * (max 12 q) * ((N - k : ℤ) + 2 : ℝ) ≤ 1 / 512 := by
      have hmax : max (12 : ℝ) q = q := max_eq_right hq12
      have hgap : ((N - k : ℤ) + 2 : ℝ) ≤ (t : ℝ) + 2 := by
        rw [hNdiff]
        have hiSucc : (i : ℝ) + 1 ≤ (t : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hi
        push_cast
        linarith
      rw [hmax]
      have hcoef : 0 ≤ M.gamma * q :=
        mul_nonneg M.shellPrefix.gamma_pos.le (by linarith [hq12])
      calc
        M.gamma * q * ((N - k : ℤ) + 2 : ℝ) ≤
            M.gamma * q * ((t : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hgap hcoef
        _ ≤ 1 / 512 := hwindow
    have hraw := aoCir_finite_even_shell_transport_of_reset_window reset
      M h hM hγ hγsmall hstate s w Qs m (m + 1) k N hQ hK hscale hN
      hw hsum (p := q) (by linarith [hq12])
      (by simpa only [max_eq_right hq12] using hqP) hwin
    have hstepRaw :
        Gaussian.positiveLpNorm μ q (cirFamilyTrace (FamilyAt N) 1) -
          Gaussian.positiveLpNorm μ q (cirFamilyTrace (FamilyAt N) 0) ≤
          19 * q * (q3ModelAmplitude M h N ^ 2 /
            (Annealed.sigmaBar M k : ℝ) ^ 2) * ((2.2 : ℝ) ^ 2 * 3120) := by
      simpa only [μ, FamilyAt, aoCirFiniteEvenFamilyAt] using hraw
    have hend := congrArg (fun X => Gaussian.positiveLpNorm μ q X)
      (hendpoint N)
    have hindex : k + ((i + 1 : ℕ) : ℤ) + 1 = N + 1 := by
      dsimp [N]
      omega
    have hAstart : A i = Gaussian.positiveLpNorm μ q
        (cirFamilyTrace (FamilyAt N) 0) := by
      change Gaussian.positiveLpNorm μ q
        (cirFamilyTrace (FamilyAt (k + (i : ℤ) + 1)) 0) = _
      rw [show k + (i : ℤ) + 1 = N by rfl]
    have hAend : A (i + 1) = Gaussian.positiveLpNorm μ q
        (cirFamilyTrace (FamilyAt N) 1) := by
      change Gaussian.positiveLpNorm μ q
        (cirFamilyTrace (FamilyAt (k + ((i + 1 : ℕ) : ℤ) + 1)) 0) = _
      rw [hindex]
      exact hend.symm
    rw [hAend, hAstart]
    have hclock := aoCir_native_shell_clock_depth M h k N (by omega) (hstate k)
    have hpow : (3 : ℝ) ^ (2 * M.gamma * ((N - k : ℤ) : ℝ)) ≤
        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hgap : ((N - k : ℤ) : ℝ) ≤ (t : ℝ) := by
        rw [hNdiff]
        have hiSucc : (i : ℝ) + 1 ≤ (t : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt hi
        push_cast
        linarith
      nlinarith [M.shellPrefix.gamma_pos.le, hgap]
    have hclock' : q3ModelAmplitude M h N ^ 2 /
        (Annealed.sigmaBar M k : ℝ) ^ 2 ≤
        (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) :=
      hclock.trans (by
        have hpow' := mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 2)
            M.shellPrefix.gamma_pos.le)
        simpa only [Int.cast_sub] using hpow')
    have hcoeff : 0 ≤ 19 * q := by positivity
    have hcap : 0 ≤ (2.2 : ℝ) ^ 2 * 3120 := by positivity
    calc
      _ ≤ 19 * q * ((9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) * ((2.2 : ℝ) ^ 2 * 3120) :=
        le_trans hstepRaw (by
          apply mul_le_mul_of_nonneg_right _ hcap
          exact mul_le_mul_of_nonneg_left hclock' hcoeff)
      _ = _ := by ring
  have htel (j : ℕ) :
      Finset.sum (Finset.range j) (fun i => A (i + 1) - A i) = A j - A 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hsumStep : Finset.sum (Finset.range t)
      (fun i => A (i + 1) - A i) ≤
      Finset.sum (Finset.range t) (fun _ =>
        19 * q * (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hstep i (Finset.mem_range.mp hi)
  have hconst : Finset.sum (Finset.range t) (fun _ : ℕ =>
      19 * q * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) =
      (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [htel t, hconst] at hsumStep
  have hfinalMem : MemLp fK (ENNReal.ofReal q) μ := by
    rw [← hfinalEq]
    exact hfamilyMem m (by omega) 1 (by norm_num) (by norm_num)
  refine ⟨hfinalMem, ?_⟩
  have hbaseBound := hbaseNorm
  have hAt : A t = lpNorm fK (ENNReal.ofReal q) μ := by
    dsimp [A]
    have he := congrArg (fun X => Gaussian.positiveLpNorm μ q X) (hendpoint m)
    have hidx : k + (t : ℤ) + 1 = m + 1 := by dsimp [k]; omega
    rw [hidx]
    exact he.symm.trans hfinalNorm
  calc
    _ = A t := hAt.symm
    _ ≤ A 0 + (t : ℝ) *
        (19 * q * (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) := by
      nlinarith [hsumStep]
    _ ≤ 900000 * M.gamma * (q + 2) +
        (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) :=
      by rw [hA0]; nlinarith [hbaseBound]

private theorem aoPerDepth_small_frame_add
    (M : ABKModel 2) (t : ℕ) (htpos : 0 < t) {q : ℝ}
    (hq12 : 12 ≤ q)
    (hwindow : M.gamma * q * ((t : ℝ) + 2) ≤ 1 / 512) :
    8 * (101 : ℝ) * ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2 ≤
      4 * M.gamma * q * (t : ℝ) := by
  have ht1 : 1 ≤ (t : ℝ) := by exact_mod_cast htpos
  have hqt : M.gamma * q * (t : ℝ) ≤ 1 / 512 := by
    have hleft := mul_le_mul_of_nonneg_left
      (show (t : ℝ) ≤ (t : ℝ) + 2 by linarith)
      (mul_nonneg M.shellPrefix.gamma_pos.le
        (by linarith [hq12] : (0 : ℝ) ≤ q))
    nlinarith [hwindow]
  have hgammaTsmall : M.gamma * (t : ℝ) ≤ 1 / (512 * 12) := by
    have hfactor := mul_le_mul_of_nonneg_right
      (show (12 : ℝ) ≤ q by exact_mod_cast hq12)
      (mul_nonneg M.shellPrefix.gamma_pos.le (by positivity : 0 ≤ (t : ℝ)))
    nlinarith [hqt]
  have hgammaSq : M.gamma ^ 2 * (t : ℝ) ^ 2 ≤
      (M.gamma * q * (t : ℝ)) / (512 * 12 * 12) := by
    have hA : 0 ≤ M.gamma * (t : ℝ) :=
      mul_nonneg M.shellPrefix.gamma_pos.le (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hgammaTsmall hA
    have h2 : M.gamma * (t : ℝ) ≤ M.gamma * q * (t : ℝ) / 12 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 12)]
      nlinarith [hqt, show 0 ≤ M.gamma * (t : ℝ) by positivity, hq12]
    have h3 := div_le_div_of_nonneg_right h2 (by norm_num : (0 : ℝ) ≤ 512 * 12)
    calc
      _ = (M.gamma * (t : ℝ)) ^ 2 := by ring
      _ ≤ (M.gamma * (t : ℝ)) / (512 * 12) := by nlinarith [h1]
      _ ≤ (M.gamma * q * (t : ℝ)) / (512 * 12 * 12) := by
        convert h3 using 1 <;> field_simp <;> ring
  have hframeCoeff :
      (8 : ℝ) * 101 * (11 / 5 : ℝ) ^ 2 / (512 * 12 * 12) ≤ 4 := by norm_num
  have hlin :
      8 * (101 : ℝ) * ((11 / 5 : ℝ) * M.gamma * (t : ℝ)) ^ 2 ≤
        4 * M.gamma * q * (t : ℝ) := by
    calc
      _ = (8 * 101 * (11 / 5 : ℝ) ^ 2) *
          (M.gamma ^ 2 * (t : ℝ) ^ 2) := by ring
      _ ≤ (8 * 101 * (11 / 5 : ℝ) ^ 2) *
          ((M.gamma * q * (t : ℝ)) / (512 * 12 * 12)) :=
        mul_le_mul_of_nonneg_left hgammaSq (by positivity)
      _ ≤ 4 * M.gamma * q * (t : ℝ) := by
        have hnonneg : 0 ≤ M.gamma * q * (t : ℝ) :=
          mul_nonneg (mul_nonneg M.shellPrefix.gamma_pos.le
            (by linarith [hq12])) (by positivity)
        nlinarith [hframeCoeff, hnonneg]
  have harg : 0 ≤ (11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le) (by positivity)
  have hargLe : (11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1) ≤
      (11 / 5 : ℝ) * M.gamma * (t : ℝ) := by
    have hstep : (t : ℝ) + 1 ≤ 2 * (t : ℝ) := by linarith
    nlinarith [M.shellPrefix.gamma_pos.le, hstep]
  have hsq : ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2 ≤
      ((11 / 5 : ℝ) * M.gamma * (t : ℝ)) ^ 2 :=
    (sq_le_sq₀ harg
      (mul_nonneg (mul_nonneg (by norm_num) M.shellPrefix.gamma_pos.le)
        (by positivity))).2 hargLe
  calc
    _ ≤ 8 * 101 * ((11 / 5 : ℝ) * M.gamma * (t : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ ≤ _ := hlin

theorem aoPerDepth_direct_common_frame_cell_bound
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ j : ℤ, nativeInductionState M h j)
    (m : ℤ) (Q : TriadicCube 2) (t : ℕ) (htpos : 0 < t)
    (hQdepth : Q ∈ descendantsAtDepth (originCube 2 m) t)
    {q : ℝ} (hq12 : 12 ≤ q) (hqP : q ≤ (smallGammaSeedP M.gamma : ℝ))
    (hwindow : M.gamma * q * ((t : ℝ) + 2) ≤ 1 / 512) :
    MemLp (fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω => traceDefect (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ))
      (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      (1017 / 1000 : ℝ) *
        (900000 * M.gamma * (q + 2) +
          (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
            (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120))) +
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let k : ℤ := m - (t : ℤ)
  let oldTrace : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet (originCube 2 k))
      (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M k : ℝ)
  let cellOld : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M k : ℝ)
  let cellNew : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ)
  have hQscale : Q.scale = k := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hQdepth
    simpa [k, originCube] using hs
  have hDirect := aoPerDepth_direct_old_frame_cell_norm reset M h hM hγ
    hγsmall hstate m Q t htpos hQdepth hq12 hqP hwindow
  have hOldID := aoPerDepth_cell_trace_identDistrib_at_frame M m Q
    (Annealed.sigmaBar M k : ℝ)
  have hOldMem : MemLp oldTrace (ENNReal.ofReal q) μ := by
    simpa only [oldTrace, μ, hQscale] using hOldID.memLp_iff.mp hDirect.1
  have hOldEq : eLpNorm oldTrace (ENNReal.ofReal q) μ =
      eLpNorm cellOld (ENNReal.ofReal q) μ := by
    simpa only [oldTrace, cellOld, μ, hQscale] using
      (hOldID.eLpNorm_eq (p := ENNReal.ofReal q)).symm
  have hOldNormEq : lpNorm oldTrace (ENNReal.ofReal q) μ =
      lpNorm cellOld (ENNReal.ofReal q) μ := by
    unfold lpNorm
    exact congrArg ENNReal.toReal hOldEq
  have hOldNorm : lpNorm oldTrace (ENNReal.ofReal q) μ ≤
      900000 * M.gamma * (q + 2) +
        (t : ℝ) * (19 * q * (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) * ((2.2 : ℝ) ^ 2 * 3120)) :=
    hOldNormEq.trans_le hDirect.2
  let sigmaOld : ℝ := Annealed.sigmaBar M k
  let sigmaNew : ℝ := Annealed.sigmaBar M m
  let rho : ℝ := sigmaNew / sigmaOld
  have hgapZ : m - k = (t : ℤ) := by dsimp [k]; omega
  have hgapR : ((m - k : ℤ) : ℝ) = (t : ℝ) := by exact_mod_cast hgapZ
  have hrho : 1 ≤ rho ∧ rho ≤ (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
    have hratio := Scalar.sigmaBar_structural_continuity M k (m - k)
      (sub_nonneg.mpr (by omega : k ≤ m))
    dsimp [rho, sigmaNew, sigmaOld]
    have hsum : k + (m - k) = m := by omega
    rw [hsum] at hratio
    rw [hgapR] at hratio
    exact hratio
  have hgammaT : M.gamma * (t : ℝ) ≤ 1 / 6144 := by
    have ht2 : 0 ≤ (t : ℝ) + 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_right
      (show (12 : ℝ) ≤ q by exact_mod_cast hq12)
      (mul_nonneg M.shellPrefix.gamma_pos.le ht2)
    nlinarith [hwindow]
  have hgammaTgammaZero : M.gamma * (t : ℝ) ≤ gammaZero := by
    exact hgammaT.trans (by norm_num [gammaZero])
  have hframeGate := Numerics.AllOrder.allorder_frame_gates
  have hpowCap : (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) ≤ 1.0008 := by
    have hexp : 2 * M.gamma * (t : ℝ) ≤ 2 * gammaZero := by
      nlinarith [M.shellPrefix.gamma_pos.le, hgammaTgammaZero]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp
    have hzero : (3 : ℝ) ^ (2 * gammaZero) < 1.0008 := by
      dsimp [gammaZero]
      exact hframeGate.2.2.2.1.trans_lt hframeGate.2.2.2.2.1
    exact hpow.trans hzero.le
  have hmult : rho * (101 / 100 : ℝ) ≤ 1017 / 1000 := by
    have hrhoCap := hrho.2.trans hpowCap
    nlinarith
  have hsmallFrameAdd := aoPerDepth_small_frame_add M t htpos hq12 hwindow
  have hadd : rho *
      (8 * (101 : ℝ) * ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2) ≤
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
    calc
      _ ≤ (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) *
          (8 * (101 : ℝ) * ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2) :=
        mul_le_mul_of_nonneg_right hrho.2 (by positivity)
      _ ≤ (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) *
          (4 * M.gamma * q * (t : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmallFrameAdd
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      _ = _ := by ring
  have hrestore (ω : Cutoff.CutoffSample 2) :
      cutoffTraceDefect M m k ω ≤
        (1017 / 1000 : ℝ) * oldTrace ω +
          4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
    have hframe := Main.main_cutoff_pathwise_frame_map M k m k ω
      (by omega) (1 / 100 : ℝ) (by norm_num)
    have hgapReal : (m : ℝ) - (k : ℝ) = (t : ℝ) := by exact_mod_cast hgapZ
    have hgap : (m : ℝ) - (k : ℝ) + 1 = (t : ℝ) + 1 := by rw [hgapReal]
    have htraceNonneg : 0 ≤ oldTrace ω := by
      dsimp [oldTrace]
      obtain ⟨Λ, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω
        (originCube 2 k)
      exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
        (Annealed.sigmaBar_characterization M k).1
    have hframe' : cutoffTraceDefect M m k ω ≤
        rho * ((101 / 100 : ℝ) * oldTrace ω +
          8 * 101 * ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2) := by
      simpa only [oldTrace, rho, sigmaOld, sigmaNew, hgap,
        show 1 + (1 / 100 : ℝ) = 101 / 100 by norm_num,
        show 8 * (1 + 1 / (1 / 100 : ℝ)) = 8 * 101 by norm_num] using hframe
    calc
      _ ≤ rho * ((101 / 100 : ℝ) * oldTrace ω +
          8 * 101 * ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2) := hframe'
      _ = rho * ((101 / 100 : ℝ) * oldTrace ω) +
          rho * (8 * 101 * ((11 / 10 : ℝ) * M.gamma * ((t : ℝ) + 1)) ^ 2) := by ring
      _ ≤ (1017 / 1000 : ℝ) * oldTrace ω +
          4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
        exact add_le_add
          (calc
            rho * ((101 / 100 : ℝ) * oldTrace ω) =
                (rho * (101 / 100 : ℝ)) * oldTrace ω := by ring
            _ ≤ (1017 / 1000 : ℝ) * oldTrace ω :=
              mul_le_mul_of_nonneg_right hmult htraceNonneg)
          hadd
  have hDomMem : MemLp (fun ω => (1017 / 1000 : ℝ) * oldTrace ω +
      4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
      (ENNReal.ofReal q) μ := by
    have hmuls := hOldMem.const_smul (1017 / 1000 : ℝ)
    have hadd' := hmuls.add (memLp_const
      (4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))))
    have heq : (fun ω => (1017 / 1000 : ℝ) * oldTrace ω +
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) =
        (1017 / 1000 : ℝ) • oldTrace + (fun _ =>
          4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) := by
      funext ω
      rfl
    rw [heq]
    exact hadd'
  have htargetMemOrigin : MemLp (cutoffTraceDefect M m k)
      (ENNReal.ofReal q) μ := by
    apply hDomMem.mono'
    · exact (Variational.cutoffTraceDefect_measurable M m k).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (Variational.cutoffTraceDefect_nonneg M m k ω)]
        exact hrestore ω
  have hpOrd : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q :=
    ENNReal.one_le_ofReal.mpr (by linarith [hq12])
  have hDomLp : lpNorm (fun ω => (1017 / 1000 : ℝ) * oldTrace ω +
      4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
      (ENNReal.ofReal q) μ ≤
      (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal q) μ +
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
    have hmulMem := hOldMem.const_smul (1017 / 1000 : ℝ)
    have htri := lpNorm_add_le (f := (1017 / 1000 : ℝ) • oldTrace)
      (g := fun _ => 4 * M.gamma * q * (t : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) hmulMem hpOrd
    have hsum : (1017 / 1000 : ℝ) • oldTrace + (fun _ =>
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) =
        (fun ω => (1017 / 1000 : ℝ) * oldTrace ω +
          4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ))) := by
      funext ω
      rfl
    rw [hsum] at htri
    have hscale : lpNorm ((1017 / 1000 : ℝ) • oldTrace)
        (ENNReal.ofReal q) μ =
        (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal q) μ := by
      rw [lpNorm_const_smul]
      norm_num
    have hqpos : 0 < q := by linarith [hq12]
    have hqnonneg : 0 ≤ q := by linarith [hq12]
    have hconstNonneg : 0 ≤ 4 * M.gamma * q * (t : ℝ) *
        (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        M.shellPrefix.gamma_pos.le) hqnonneg) (by positivity))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
    have hconst : lpNorm (fun _ : Cutoff.CutoffSample 2 =>
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
        (ENNReal.ofReal q) μ =
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
      rw [lpNorm_const' (ENNReal.ofReal_ne_zero_iff.mpr hqpos)
        ENNReal.ofReal_ne_top]
      simp only [Real.norm_of_nonneg hconstNonneg, probReal_univ,
        Real.one_rpow, mul_one]
    rw [hscale, hconst] at htri
    exact htri
  have htargetLpOrigin : lpNorm (cutoffTraceDefect M m k)
      (ENNReal.ofReal q) μ ≤
      (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal q) μ +
        4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)) := by
    calc
      _ ≤ lpNorm (fun ω => (1017 / 1000 : ℝ) * oldTrace ω +
          4 * M.gamma * q * (t : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (t : ℝ)))
          (ENNReal.ofReal q) μ := by
        apply lpNorm_mono_real hDomMem
        intro ω
        rw [Real.norm_of_nonneg (Variational.cutoffTraceDefect_nonneg M m k ω)]
        exact hrestore ω
      _ ≤ _ := hDomLp
  have hNewID := aoPerDepth_cell_trace_identDistrib_at_frame M m Q
    (Annealed.sigmaBar M m : ℝ)
  have hOriginMem : MemLp (fun ω => traceDefect
      (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ)) (ENNReal.ofReal q) μ := by
    change MemLp (fun ω => traceDefect
      (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ)) (ENNReal.ofReal q) μ at htargetMemOrigin
    exact htargetMemOrigin
  have hOriginMemQ : MemLp (fun ω => traceDefect
      (cubeSet (originCube 2 Q.scale)) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M m : ℝ)) (ENNReal.ofReal q)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [μ, hQscale] using hOriginMem
  have hCellMem : MemLp cellNew (ENNReal.ofReal q) μ := by
    simpa only [cellNew, μ] using hNewID.memLp_iff.mpr hOriginMemQ
  have hNewEq0 : eLpNorm cellNew (ENNReal.ofReal q) μ =
      eLpNorm (fun ω => traceDefect (cubeSet (originCube 2 k))
        (Cutoff.coefficientCutoff M.nu m ω).toFun
        (Annealed.sigmaBar M m : ℝ)) (ENNReal.ofReal q) μ := by
    simpa only [cellNew, μ, hQscale] using
      (hNewID.eLpNorm_eq (p := ENNReal.ofReal q))
  have hNewEq : eLpNorm cellNew (ENNReal.ofReal q) μ =
      eLpNorm (cutoffTraceDefect M m k) (ENNReal.ofReal q) μ := by
    change eLpNorm cellNew (ENNReal.ofReal q) μ =
      eLpNorm (fun ω => traceDefect (cubeSet (originCube 2 k))
        (Cutoff.coefficientCutoff M.nu m ω).toFun
        (Annealed.sigmaBar M m : ℝ)) (ENNReal.ofReal q) μ
    exact hNewEq0
  have hNewNormEq : lpNorm cellNew (ENNReal.ofReal q) μ =
      lpNorm (cutoffTraceDefect M m k) (ENNReal.ofReal q) μ := by
    unfold lpNorm
    exact congrArg ENNReal.toReal hNewEq
  refine ⟨hCellMem, ?_⟩
  calc
    _ = lpNorm (cutoffTraceDefect M m k) (ENNReal.ofReal q) μ := hNewNormEq
    _ ≤ _ := htargetLpOrigin.trans (by
      nlinarith [hOldNorm])

end
end ASDExplicitGamma.AllOrder
