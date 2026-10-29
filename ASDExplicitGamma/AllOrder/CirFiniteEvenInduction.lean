/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenStepTransport
public import ASDExplicitGamma.AllOrder.ProfileResetAdapter
public import ASDExplicitGamma.AllOrder.CirAveraging
public import ASDExplicitGamma.Inverse.HistoryTraceMonotone
public import ASDExplicitGamma.Cold.NativeSubadditivity
public import ASDExplicitGamma.Gaussian.P12Regularized
public import ASDExplicitGamma.Statements.NativeInductionState

/-! # Small-gamma finite-even induction from the actual shell transport -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Cold
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

noncomputable section

private theorem aoCir_cutoff_trace_subadditive_in_frame (M : ABKModel 2)
    (n : ℤ) (Q : TriadicCube 2) (r : ℕ) (σ : ℝ) (hσ : 0 < σ)
    (ω : Cutoff.CutoffSample 2) :
    traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun σ ≤
      descendantsAverage Q r (fun R =>
        traceDefect (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun σ) := by
  have h := Inverse.history_weighted_trace_mono
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun)
    (descendantsAverageBlockMat Q r (fun R =>
      coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun))
    σ hσ (Variational.cutoff_coarse_matrix_subadditive M n Q r ω)
  have he : descendantsAverage Q r (fun R =>
      traceDefect (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun σ) =
      σ⁻¹ * Matrix.trace
          (descendantsAverageBlockMat Q r (fun R =>
            coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun)).upperLeft +
        σ * Matrix.trace
          (descendantsAverageBlockMat Q r (fun R =>
            coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu n ω).toFun)).lowerRight - 4 := by
    simp only [traceDefect, Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
    dsimp only [descendantsAverageBlockMat, descendantsAverageMat]
    simp only [sub_eq_add_neg, descendantsAverage_add, descendantsAverage_mul_left,
      descendantsAverage_const]
  rw [he]
  exact h

private theorem aoCir_step_trace_eq_partial
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

private theorem aoCir_descendant_closure_subset {Q : TriadicCube 2} {r : ℕ}
    {R : TriadicCube 2} (hR : R ∈ descendantsAtDepth Q r) :
    closure (openCubeSet R) ⊆ closure (cubeSet Q) := by
  exact closure_mono ((openCubeSet_subset_of_mem_descendantsAtDepth hR).trans
    (openCubeSet_subset_cubeSet Q))

private theorem aoCir_squareCell_closure_subset {Q : TriadicCube 2} {r : ℕ}
    (C : SquareCells Q r) : closure (openCubeSet C.val) ⊆ closure (cubeSet Q) :=
  aoCir_descendant_closure_subset C.property

private theorem aoCir_squareCellMean_fin_average (Q : TriadicCube 2) (r : ℕ)
    (f : SquareCells Q r → ℝ) :
    Cold.squareCellMean Q r f =
      ((Fintype.card (SquareCells Q r) : ℝ)⁻¹ *
        ∑ i : Fin (9 ^ r), f (Cold.coldCellEquiv Q r i)) := by
  unfold Cold.squareCellMean
  rw [show (descendantsAtDepth Q r).card = 9 ^ r by
    rw [descendantsAtDepth_card]
    norm_num]
  rw [show Fintype.card (SquareCells Q r) = 9 ^ r by exact Cold.cold_square_cells_card Q r]
  rw [← Equiv.sum_comp (Cold.coldCellEquiv Q r) f]

private theorem aoCir_squareCellMean_eq_descendantsAverage
    {Q : TriadicCube 2} {r : ℕ} (f : TriadicCube 2 → ℝ) :
    Cold.squareCellMean Q r (fun C => f C.val) = descendantsAverage Q r f := by
  unfold Cold.squareCellMean descendantsAverage
  congr 1
  exact Finset.sum_attach (descendantsAtDepth Q r) f

private theorem aoCir_nativeChildCell_fin_eq (n : ℤ) (i : Fin (9 ^ 8)) :
    (Cold.coldCellEquiv (originCube 2 (n + 8)) 8 i).val =
      Cold.coldNativeChildCell n 0 8 i := by
  rfl

private theorem aoCir_start_squareCellMean_lpNorm_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (hstate : nativeInductionState M h n)
    {p : ℕ} (hpEven : Even p) (hpMin : 12 ≤ p)
    (hMoment : ∀ q : ℕ, 12 ≤ q → q ≤ p → Even q →
      MemLp (cutoffTraceDefect M n n) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M n n) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (q : ℝ)) :
    MemLp
      (fun ω => Cold.squareCellMean (originCube 2 (n + 8)) 8
        (fun C => Cold.coldNativeCellTrace M n C.val ω))
      (p : ℝ≥0∞) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm
      (fun ω => Cold.squareCellMean (originCube 2 (n + 8)) 8
        (fun C => Cold.coldNativeCellTrace M n C.val ω))
      (p : ℝ≥0∞) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma +
        144 * (900000 * M.gamma) *
          (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
            9 * (p : ℝ) / (3 ^ 16 : ℝ)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let root := originCube 2 (n + 8)
  let mean := Cold.coldNativeMean M n 0
  let centered : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (∑ i : Fin (9 ^ 8),
      (Cold.coldNativeCellTrace M n (Cold.coldNativeChildCell n 0 8 i) ω - mean)) /
        (3 ^ 16 : ℝ)
  have hMomentP := hMoment p hpMin (by omega) hpEven
  have hCellMem (i : Fin (9 ^ 8)) :
      MemLp (Cold.coldNativeCellTrace M n (Cold.coldNativeChildCell n 0 8 i))
        (p : ℝ≥0∞) μ := by
    have hscale := Cold.coldNativeChildCell_scale n (by norm_num : 0 ≤ 8) i
    have hscale' : (Cold.coldNativeChildCell n 0 8 i).scale = n := by
      simpa using hscale
    have hrootMem : MemLp (cutoffTraceDefect M n
        (Cold.coldNativeChildCell n 0 8 i).scale) (p : ℝ≥0∞) μ := by
      simpa only [μ, hscale'] using hMomentP.1
    exact (Cold.coldNativeCellTrace_memLp_iff M n
      (Cold.coldNativeChildCell n 0 8 i) (p : ℝ≥0∞)).2 hrootMem
  have htermMem (i : Fin (9 ^ 8)) :
      MemLp (fun ω => Cold.coldNativeCellTrace M n
        (Cold.coldNativeChildCell n 0 8 i) ω - mean) (p : ℝ≥0∞) μ :=
    (hCellMem i).sub (memLp_const mean)
  have hcenterCapRaw := aoCir_native_child_average_centered_bound
    M h hM n hpEven hpMin hMoment
  have hmeanNonneg : 0 ≤ mean := by
    dsimp [mean, Cold.coldNativeMean]
    exact integral_nonneg (fun ω => Cold.coldNativeTrace_nonneg M n 0 ω)
  have hmean0 : mean ≤ (3 / 50 : ℝ) * theta M :=
    Cold.coldNativeMean_zero_le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 50)
        (div_nonneg (le_of_lt M.shellPrefix.gamma_pos) (by norm_num [gammaZero])))
      hstate.1
  have hmeanFactor : (3 / 50 : ℝ) / gammaZero ≤ 177 := by
    norm_num [gammaZero]
  have hmeanBound : mean ≤ 177 * M.gamma := by
    calc
      mean ≤ (3 / 50 : ℝ) * theta M := hmean0
      _ = ((3 / 50 : ℝ) / gammaZero) * M.gamma := by rw [theta]; ring
      _ ≤ 177 * M.gamma :=
        mul_le_mul_of_nonneg_right hmeanFactor M.shellPrefix.gamma_pos.le
  have hmeanCell (i : Fin (9 ^ 8)) :
      (∫ ω, Cold.coldNativeCellTrace M n
        (Cold.coldNativeChildCell n 0 8 i) ω ∂μ) = mean := by
    rw [Cold.coldNativeCellTrace_integral]
    have hscale := Cold.coldNativeChildCell_scale n (by norm_num : 0 ≤ 8) i
    simp [mean, Cold.coldNativeMean, Cold.coldNativeTrace, hscale]
  have hcenterDef :
      centered = ((3 ^ 16 : ℝ)⁻¹) •
        (fun ω => ∑ i : Fin (9 ^ 8),
          (Cold.coldNativeCellTrace M n
            (Cold.coldNativeChildCell n 0 8 i) ω - mean)) := by
    funext ω
    simp only [centered, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have hcenterMem : MemLp centered (p : ℝ≥0∞) μ := by
    rw [hcenterDef]
    have hsumMem : MemLp
        (fun ω => ∑ i ∈ Finset.univ,
          (Cold.coldNativeCellTrace M n
            (Cold.coldNativeChildCell n 0 8 i) ω - mean)) (p : ℝ≥0∞) μ := by
      exact memLp_finsetSum Finset.univ (by
        intro i hi
        exact htermMem i)
    have hsumMem' : MemLp
        (fun ω => ∑ i : Fin (9 ^ 8),
          (Cold.coldNativeCellTrace M n
            (Cold.coldNativeChildCell n 0 8 i) ω - mean)) (p : ℝ≥0∞) μ := by
      simpa using hsumMem
    exact hsumMem'.const_smul ((3 ^ 16 : ℝ)⁻¹)
  have hcenteredFinEq :
      centered = fun ω =>
        (∑ i : Fin (9 ^ 8),
          (Cold.coldNativeCellTrace M n
            (Cold.coldNativeChildCell n 0 8 i) ω -
            ∫ ω', Cold.coldNativeCellTrace M n
              (Cold.coldNativeChildCell n 0 8 i) ω' ∂μ)) / (3 ^ 16 : ℝ) := by
    funext ω
    change
      (∑ i : Fin (9 ^ 8),
        (Cold.coldNativeCellTrace M n
          (Cold.coldNativeChildCell n 0 8 i) ω - mean)) / (3 ^ 16 : ℝ) = _
    apply congrArg (fun x : ℝ => x / (3 ^ 16 : ℝ))
    apply Finset.sum_congr rfl
    intro i _
    rw [hmeanCell i]
  have hcenterCap :
      lpNorm centered (p : ℝ≥0∞) μ ≤
        144 * (900000 * M.gamma) *
          (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
            9 * (p : ℝ) / (3 ^ 16 : ℝ)) := by
    rw [hcenteredFinEq]
    exact hcenterCapRaw
  have hcenterEq :
      (fun ω => Cold.squareCellMean root 8
        (fun C => Cold.coldNativeCellTrace M n C.val ω - mean)) = centered := by
    funext ω
    rw [aoCir_squareCellMean_fin_average]
    have hcard : (Fintype.card (SquareCells root 8) : ℝ) = (3 : ℝ) ^ 16 := by
      rw [Cold.cold_square_cells_card]
      norm_num
    rw [hcard]
    have hsumEq :
        (∑ i : Fin (9 ^ 8),
          (Cold.coldNativeCellTrace M n
            (Cold.coldCellEquiv root 8 i).val ω - mean)) =
        (∑ i : Fin (9 ^ 8),
          (Cold.coldNativeCellTrace M n
            (Cold.coldNativeChildCell n 0 8 i) ω - mean)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [aoCir_nativeChildCell_fin_eq n i]
    simp only [centered, div_eq_mul_inv]
    rw [hsumEq]
    ring
  have hdecomp :
      (fun ω => Cold.squareCellMean root 8
        (fun C => Cold.coldNativeCellTrace M n C.val ω)) =
        fun ω => centered ω + mean := by
    funext ω
    calc
      Cold.squareCellMean root 8
          (fun C => Cold.coldNativeCellTrace M n C.val ω) =
        Cold.squareCellMean root 8
          (fun C => (Cold.coldNativeCellTrace M n C.val ω - mean) + mean) := by
            congr 1
            funext C
            ring
      _ = Cold.squareCellMean root 8
            (fun C => Cold.coldNativeCellTrace M n C.val ω - mean) +
          Cold.squareCellMean root 8 (fun _ => mean) :=
        Cold.squareCellMean_add root 8 _ _
      _ = centered ω + mean := by
        rw [congrFun hcenterEq ω, Cold.squareCellMean_const]
  have hsum :
      centered + (fun _ => mean) =
        fun ω => Cold.squareCellMean root 8
          (fun C => Cold.coldNativeCellTrace M n C.val ω) := by
    funext ω
    exact (congrFun hdecomp ω).symm
  have htri := lpNorm_add_le hcenterMem (g := fun _ : Cutoff.CutoffSample 2 => mean)
    (show (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) by exact_mod_cast (show 1 ≤ p by omega))
  rw [hsum] at htri
  rw [lpNorm_const' (show (p : ℝ≥0∞) ≠ 0 by
    exact_mod_cast (show p ≠ 0 by omega)) ENNReal.coe_ne_top mean] at htri
  simp only [Real.norm_of_nonneg hmeanNonneg, probReal_univ, Real.one_rpow, mul_one] at htri
  have hmean700 : mean ≤ 700 * M.gamma :=
    hmeanBound.trans (mul_le_mul_of_nonneg_right (by norm_num : (177 : ℝ) ≤ 700)
      M.shellPrefix.gamma_pos.le)
  have htarget : lpNorm centered (p : ℝ≥0∞) μ + mean ≤
      144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
          9 * (p : ℝ) / (3 ^ 16 : ℝ)) + 700 * M.gamma := by
    linarith [hcenterCap, hmean700]
  have hstartMem : MemLp
      (fun ω => Cold.squareCellMean root 8
        (fun C => Cold.coldNativeCellTrace M n C.val ω)) (p : ℝ≥0∞) μ := by
    rw [← hsum]
    exact hcenterMem.add (memLp_const mean)
  have hstartBound : lpNorm
      (fun ω => Cold.squareCellMean root 8
        (fun C => Cold.coldNativeCellTrace M n C.val ω))
      (p : ℝ≥0∞) μ ≤
      700 * M.gamma +
        144 * (900000 * M.gamma) *
          (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
            9 * (p : ℝ) / (3 ^ 16 : ℝ)) := by
    linarith
  exact ⟨hstartMem, hstartBound⟩

private theorem aoCir_uniform_child_average_eq_squareCellMean
    (M : ABKModel 2) (h : ℝ) (coeffLabel frameLabel parentScale : ℤ) (r : ℕ)
    (ell : ℤ) (hK : closure (cubeSet (originCube 2 parentScale)) ⊆
      openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    let root := originCube 2 parentScale
    let d := descendantsAtDepth root r
    let s := Finset.attach d
    let w : SquareCells root r → ℝ := fun _ => (d.card : ℝ)⁻¹
    let Q : SquareCells root r → TriadicCube 2 := fun C => C.val
    cirFamilyTrace
        ((aoCirFiniteEvenFamilyAt s w Q
          M h parentScale frameLabel
          (fun C => aoCir_squareCell_closure_subset C)
          (by intro C _hC; positivity)
          (by
            classical
            have hcardPos : 0 < (d.card : ℝ) := by
              change 0 < ((descendantsAtDepth root r).card : ℝ)
              rw [descendantsAtDepth_card]
              positivity
            dsimp [s, w]
            simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
            field_simp [ne_of_gt hcardPos])) (coeffLabel + 1)) 0 ω =
      Cold.squareCellMean (originCube 2 parentScale) r
        (fun C => traceDefect (cubeSet C.val)
          (Cutoff.coefficientCutoff M.nu coeffLabel ω).toFun
          (Annealed.sigmaBar M frameLabel : ℝ)) := by
  classical
  let root := originCube 2 parentScale
  let d := descendantsAtDepth root r
  let s : Finset (SquareCells root r) := Finset.attach d
  let w : SquareCells root r → ℝ := fun _ => (d.card : ℝ)⁻¹
  let Q : SquareCells root r → TriadicCube 2 := fun C => C.val
  have hcardPos : 0 < (d.card : ℝ) := by
    change 0 < ((descendantsAtDepth root r).card : ℝ)
    rw [descendantsAtDepth_card]
    positivity
  have htrace (C : SquareCells root r) :
      Gaussian.squareTrace (Q C) M.nu (Annealed.sigmaBar M frameLabel)
        (cirSquareRestrictionCLM (Q C)
          (aoCir_squareCell_closure_subset C)
          (modelInsertedScalar (closure (cubeSet (originCube 2 parentScale))) coeffLabel 0 ω)) =
      traceDefect (cubeSet C.val) (Cutoff.coefficientCutoff M.nu coeffLabel ω).toFun
        (Annealed.sigmaBar M frameLabel : ℝ) := by
    have h := aoCir_step_trace_eq_partial M (Q C) parentScale ell
      (aoCir_squareCell_closure_subset C) hK coeffLabel (coeffLabel + 1) frameLabel
      (by omega) 0 ω
    have hzero : Model.partialInsertedCoefficient M coeffLabel 0 ω =
        Cutoff.coefficientCutoff M.nu coeffLabel ω := by
      ext x i j
      simp [Model.partialInsertedCoefficient, RegCoeffField.add_apply,
        RegCoeffField.smul_apply]
    simpa only [show coeffLabel + 1 - 1 = coeffLabel by omega, hzero] using h
  have hsum : ∑ C ∈ s, w C = 1 := by
    dsimp [s, w]
    simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    field_simp [ne_of_gt hcardPos]
  have hfamily := aoCirFiniteEvenFamilyAt_trace s w Q M h parentScale frameLabel
    (fun C => aoCir_squareCell_closure_subset C)
    (by intro C _hC; positivity) hsum (coeffLabel + 1) 0 ω
  have hfamily' : cirFamilyTrace
      (aoCirFiniteEvenFamilyAt s w Q M h parentScale frameLabel
        (fun C => aoCir_squareCell_closure_subset C)
        (by intro C _hC; positivity) hsum (coeffLabel + 1)) 0 ω =
      ∑ C ∈ s, w C * Gaussian.squareTrace (Q C) M.nu
        (Annealed.sigmaBar M frameLabel)
        (cirSquareRestrictionCLM (Q C) (aoCir_squareCell_closure_subset C)
          (modelInsertedScalar (closure (cubeSet root)) coeffLabel 0 ω)) := by
    simpa only [show coeffLabel + 1 - 1 = coeffLabel by omega] using hfamily
  change cirFamilyTrace
      (aoCirFiniteEvenFamilyAt s w Q M h parentScale frameLabel
        (fun C => aoCir_squareCell_closure_subset C)
        (by intro C _hC; positivity) hsum (coeffLabel + 1)) 0 ω = _
  rw [hfamily']
  have hterms : (∑ C ∈ s, w C *
      Gaussian.squareTrace (Q C) M.nu (Annealed.sigmaBar M frameLabel)
        (cirSquareRestrictionCLM (Q C) (aoCir_squareCell_closure_subset C)
          (modelInsertedScalar (closure (cubeSet root)) coeffLabel 0 ω))) =
      ∑ C ∈ s, w C * traceDefect (cubeSet C.val)
        (Cutoff.coefficientCutoff M.nu coeffLabel ω).toFun
        (Annealed.sigmaBar M frameLabel : ℝ) := by
    apply Finset.sum_congr rfl
    intro C _hC
    rw [htrace C]
  rw [hterms]
  let f : TriadicCube 2 → ℝ := fun C =>
    traceDefect (cubeSet C) (Cutoff.coefficientCutoff M.nu coeffLabel ω).toFun
      (Annealed.sigmaBar M frameLabel : ℝ)
  have hweighted : (∑ C ∈ s, w C * f C.val) =
      (d.card : ℝ)⁻¹ * ∑ C ∈ d, f C := by
    change (∑ C ∈ Finset.attach d, (d.card : ℝ)⁻¹ * f C.val) = _
    calc
      _ = ∑ C ∈ d, (d.card : ℝ)⁻¹ * f C :=
        Finset.sum_attach d (fun C => (d.card : ℝ)⁻¹ * f C)
      _ = (d.card : ℝ)⁻¹ * ∑ C ∈ d, f C := by rw [Finset.mul_sum]
  have hattach : (∑ C : SquareCells root r, f C.val) =
      ∑ C ∈ d, f C := by
    exact Finset.sum_attach d f
  unfold Cold.squareCellMean
  rw [hattach, hweighted]

private theorem aoCir_parent_closure_inside_next_open (m : ℤ) :
    closure (cubeSet (originCube 2 m)) ⊆ openCubeSet (originCube 2 (m + 1)) := by
  rw [Algsuperdiff.Section3.Provider.Whitney.closure_cubeSet_eq_closedBall]
  rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
  have hscale : (3 : ℝ) ^ (m + 1) = (3 : ℝ) ^ m * 3 := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) m 1]
    norm_num
  have hrad : Homogenization.cubeRadius (originCube 2 m) <
      Homogenization.cubeRadius (originCube 2 (m + 1)) := by
    simp only [Homogenization.cubeRadius, Homogenization.cubeScaleFactor_originCube]
    rw [hscale]
    have hp : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
    nlinarith
  have hcenter : Homogenization.cubeCenter (originCube 2 m) =
      Homogenization.cubeCenter (originCube 2 (m + 1)) := by
    ext i
    simp [Homogenization.cubeCenter, originCube]
  rw [hcenter]
  exact Metric.closedBall_subset_ball hrad

private theorem aoCir_traceDefect_cutoff_measurable_at_sigma
    (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ) (σ : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun σ) := by
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n
  have hX : Measurable X := by simpa [X] using Cutoff.measurable_coefficientCutoff M.nu n
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) := by
    intro ω
    simpa [X] using Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω
  have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet hX hEll Q
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet
    hX hEll Q
  have hTraceUL : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
  have hTraceLR : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
  change Measurable (fun ω => σ⁻¹ *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft +
      σ * Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight - 4)
  exact (hTraceUL.const_mul _).add (hTraceLR.const_mul _) |>.sub measurable_const

private theorem aoCir_squareCell_scale {Q : TriadicCube 2} {r : ℕ}
    (a : SquareCells Q r) : a.val.scale = Q.scale - (r : ℤ) :=
  Homogenization.scale_eq_sub_of_mem_descendantsAtDepth
    (Q := Q) (R := a.val) (n := r) a.property

private theorem aoCir_start_average_bound_of_prev_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {m : ℤ} {p : ℕ} (hp12 : 12 ≤ p) (hpEven : Even p)
    (hpP : p ≤ smallGammaSeedP M.gamma)
    (hprev : ∀ q : ℕ, 12 ≤ q → Even q → q ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M (m - 8) (m - 8)) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M (m - 8) (m - 8)) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (q : ℝ)) :
    MemLp (fun ω => Cold.squareCellMean (originCube 2 m) 8
        (fun C => Cold.coldNativeCellTrace M (m - 8) C.val ω))
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => Cold.squareCellMean (originCube 2 m) 8
        (fun C => Cold.coldNativeCellTrace M (m - 8) C.val ω))
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma + 144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) + 9 * (p : ℝ) / (3 ^ 16 : ℝ)) := by
  let n : ℤ := m - 8
  have hMoment : ∀ q : ℕ, 12 ≤ q → q ≤ p → Even q →
      MemLp (cutoffTraceDefect M n n) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M n n) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (q : ℝ) := by
    intro q hqMin hqp hqEven
    have hqP : q ≤ smallGammaSeedP M.gamma := le_trans hqp hpP
    simpa only [n] using hprev q hqMin hqEven hqP
  have hstart := aoCir_start_squareCellMean_lpNorm_le M h hM n (hstate n)
    hpEven hp12 hMoment
  have hroot : originCube 2 (n + 8) = originCube 2 m := by
    congr 1
    dsimp [n]
    omega
  rw [hroot] at hstart
  refine ⟨?_, ?_⟩
  · simpa only [ENNReal.ofReal_natCast] using hstart.1
  · simpa only [ENNReal.ofReal_natCast] using hstart.2

-- The constructor-name linter unfolds the dependent `MemLp` family in this
-- large transport signature until its local heartbeat budget expires. The
-- theorem itself elaborates at default heartbeats; scope this single linter
-- off rather than changing any proof heartbeat setting.
set_option linter.constructorNameAsVariable false in
private theorem aoCir_old_frame_trace_bound_of_start
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {m : ℤ} {p : ℕ} (hp12 : 12 ≤ p)
    (hpP : p ≤ smallGammaSeedP M.gamma)
    (hstart : MemLp (fun ω => Cold.squareCellMean (originCube 2 m) 8
        (fun C => Cold.coldNativeCellTrace M (m - 8) C.val ω))
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => Cold.squareCellMean (originCube 2 m) 8
        (fun C => Cold.coldNativeCellTrace M (m - 8) C.val ω))
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma + 144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) + 9 * (p : ℝ) / (3 ^ 16 : ℝ))) :
    MemLp (fun ω => traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M (m - 8) : ℝ))
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => traceDefect (cubeSet (originCube 2 m))
        (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M (m - 8) : ℝ))
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma + 144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) + 9 * (p : ℝ) / (3 ^ 16 : ℝ)) +
      8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
  classical
  let n : ℤ := m - 8
  let root : TriadicCube 2 := originCube 2 m
  let d := descendantsAtDepth root 8
  let s : Finset (SquareCells root 8) := Finset.attach d
  let w : SquareCells root 8 → ℝ := fun _ => (d.card : ℝ)⁻¹
  let Q : SquareCells root 8 → TriadicCube 2 := fun C => C.val
  let hQ : ∀ a, closure (openCubeSet (Q a)) ⊆ closure (cubeSet root) :=
    fun C => aoCir_squareCell_closure_subset C
  let hK : closure (cubeSet root) ⊆ openCubeSet (originCube 2 (m + 1)) :=
    aoCir_parent_closure_inside_next_open m
  have hn8 : n + 8 = m := by dsimp [n]; omega
  have hcardPos : 0 < (d.card : ℝ) := by
    change 0 < ((descendantsAtDepth root 8).card : ℝ)
    rw [descendantsAtDepth_card]
    positivity
  have hw : ∀ a ∈ s, 0 ≤ w a := by
    intro a ha
    dsimp [w]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  have hsum : ∑ a ∈ s, w a = 1 := by
    dsimp [s, w]
    simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    field_simp [ne_of_gt hcardPos]
  have hscale : ∀ a ∈ s, (Q a).scale = n := by
    intro a ha
    have h' : a.val.scale = root.scale - 8 := aoCir_squareCell_scale a
    have hrootScale : root.scale = m := rfl
    rw [hrootScale] at h'
    simpa [Q, n] using h'
  let FamilyAt := aoCirFiniteEvenFamilyAt s w Q M h m n hQ hw hsum
  have hstartEq :
      (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω) =
        fun ω => Cold.squareCellMean root 8
          (fun C => Cold.coldNativeCellTrace M n C.val ω) := by
    funext ω
    have h := aoCir_uniform_child_average_eq_squareCellMean M h n n m 8 (m + 1) hK ω
    simpa only [FamilyAt, n, Cold.coldNativeCellTrace] using h
  have hstartMem : MemLp (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω)
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [hstartEq]
    simpa only [root, n] using hstart.1
  have hstartNorm : lpNorm (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω)
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma + 144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
          9 * (p : ℝ) / (3 ^ 16 : ℝ)) := by
    rw [hstartEq]
    simpa only [root, n] using hstart.2
  have htrace : ∀ j t ω, cirFamilyTrace (FamilyAt j) t ω =
      ∑ a ∈ s, w a * Gaussian.squareTrace (Q a) M.nu
        (Annealed.sigmaBar M n)
        (cirSquareRestrictionCLM (Q a) (hQ a)
          (modelInsertedScalar (closure (cubeSet (originCube 2 m))) (j - 1) t ω)) := by
    intro j t ω
    simpa [FamilyAt, n, root] using
      aoCirFiniteEvenFamilyAt_trace s w Q M h m n hQ hw hsum j t ω
  have hendpoint :
      (fun ω => cirFamilyTrace (FamilyAt m) 1 ω) =
        fun ω => cirFamilyTrace (FamilyAt (m + 1)) 0 ω := by
    exact aoCir_finite_even_family_succ_endpoint FamilyAt s w Q M h m (m + 1) n m
      hQ hK hw hsum htrace
  have hfinalMemSource := aoCir_reset_square_family_memLp reset M h hM hγ hγsmall
    hstate s w Q m (m + 1) n m hQ hK hscale (by dsimp [n]; omega) hw hsum
    (q3ModelAmplitude M h m) (q3ModelLength m) (p : ℝ)
    (by exact_mod_cast (show 1 ≤ p by omega)) 1 (by norm_num) (by norm_num)
  have hfinalMem : MemLp (fun ω => cirFamilyTrace (FamilyAt m) 1 ω)
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [FamilyAt, aoCirFiniteEvenFamilyAt] using hfinalMemSource.1
  have htrans := aoCir_finite_even_eight_shell_transport_of_reset reset
    M h hM hγ hγsmall hstate s w Q m (m + 1) n hQ hK hscale hw hsum
    (show 12 ≤ (p : ℝ) by exact_mod_cast hp12)
    (by exact_mod_cast hpP)
  have htrans' : Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure
        (p : ℝ) (cirFamilyTrace (FamilyAt m) 1) -
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure
        (p : ℝ) (cirFamilyTrace (FamilyAt (n + 1)) 0) ≤
      8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
    simpa [FamilyAt, n, hn8] using htrans
  have hfinalNormEq :
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ)
        (cirFamilyTrace (FamilyAt m) 1) =
      lpNorm (fun ω => cirFamilyTrace (FamilyAt m) 1 ω) (ENNReal.ofReal (p : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [Gaussian.positiveLpNorm_eq_eLpNorm_toReal
      (Cutoff.cutoffSampleLaw M).toMeasure (by positivity) _
      (cirFamilyTrace_nonneg (FamilyAt m) 1) hfinalMem]
    rfl
  have hstartNormEq :
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ)
        (cirFamilyTrace (FamilyAt (n + 1)) 0) =
      lpNorm (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω) (ENNReal.ofReal (p : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [Gaussian.positiveLpNorm_eq_eLpNorm_toReal
      (Cutoff.cutoffSampleLaw M).toMeasure (by positivity) _
      (cirFamilyTrace_nonneg (FamilyAt (n + 1)) 0) hstartMem]
    rfl
  have hOldPoint (ω : Cutoff.CutoffSample 2) :
      traceDefect (cubeSet root) (Cutoff.coefficientCutoff M.nu m ω).toFun
          (Annealed.sigmaBar M n : ℝ) ≤ cirFamilyTrace (FamilyAt m) 1 ω := by
    have hmono := aoCir_cutoff_trace_subadditive_in_frame M m root 8
      (Annealed.sigmaBar M n) (Annealed.sigmaBar_characterization M n).1 ω
    have havg : descendantsAverage root 8 (fun R =>
        traceDefect (cubeSet R)
          (Cutoff.coefficientCutoff M.nu m ω).toFun
          (Annealed.sigmaBar M n : ℝ)) = cirFamilyTrace (FamilyAt m) 1 ω := by
      have hu := aoCir_uniform_child_average_eq_squareCellMean M h m n m 8
        (m + 1) hK ω
      have hu' : cirFamilyTrace (FamilyAt (m + 1)) 0 ω =
          Cold.squareCellMean root 8 (fun C =>
            traceDefect (cubeSet C.val)
              (Cutoff.coefficientCutoff M.nu m ω).toFun
              (Annealed.sigmaBar M n : ℝ)) := by
        simpa only [FamilyAt, root, s, w, Q] using hu
      calc
        _ = Cold.squareCellMean root 8 (fun C =>
              traceDefect (cubeSet C.val)
                (Cutoff.coefficientCutoff M.nu m ω).toFun
                (Annealed.sigmaBar M n : ℝ)) :=
          (aoCir_squareCellMean_eq_descendantsAverage
            (Q := root) (r := 8) (fun R =>
              traceDefect (cubeSet R)
                (Cutoff.coefficientCutoff M.nu m ω).toFun
                (Annealed.sigmaBar M n : ℝ))).symm
        _ = cirFamilyTrace (FamilyAt (m + 1)) 0 ω := hu'.symm
        _ = cirFamilyTrace (FamilyAt m) 1 ω := (congrFun hendpoint ω).symm
    exact hmono.trans_eq havg
  have hOldNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ traceDefect (cubeSet root) (Cutoff.coefficientCutoff M.nu m ω).toFun
        (Annealed.sigmaBar M n : ℝ) := by
    obtain ⟨Λ, hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω root
    exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M n).1
  let oldTrace : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet root) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M n : ℝ)
  have hOldMeas : Measurable oldTrace := by
    simpa [oldTrace] using
      aoCir_traceDefect_cutoff_measurable_at_sigma M root m (Annealed.sigmaBar M n)
  have hOldMem : MemLp oldTrace (ENNReal.ofReal (p : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply hfinalMem.mono'
    · exact hOldMeas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (hOldNonneg ω)]
        exact hOldPoint ω
  have hOldLp : lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm (fun ω => cirFamilyTrace (FamilyAt m) 1 ω) (ENNReal.ofReal (p : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply lpNorm_mono_real hfinalMem
    intro ω
    rw [Real.norm_of_nonneg (hOldNonneg ω)]
    exact hOldPoint ω
  have hOldEq' : Gaussian.positiveLpNorm
      (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ) oldTrace =
      lpNorm oldTrace (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [Gaussian.positiveLpNorm_eq_eLpNorm_toReal
      (Cutoff.cutoffSampleLaw M).toMeasure (by positivity) _ hOldNonneg hOldMem]
    rfl
  have hOldBound : Gaussian.positiveLpNorm
      (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ) oldTrace ≤
      lpNorm (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω)
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure +
      8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
    calc
      Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ) oldTrace =
          lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
            (Cutoff.cutoffSampleLaw M).toMeasure := hOldEq'
      _ ≤ lpNorm (fun ω => cirFamilyTrace (FamilyAt m) 1 ω)
            (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := hOldLp
      _ = Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ)
            (cirFamilyTrace (FamilyAt m) 1) := hfinalNormEq.symm
      _ ≤ Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure (p : ℝ)
            (cirFamilyTrace (FamilyAt (n + 1)) 0) +
          8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
            (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
              linarith [htrans']
      _ = lpNorm (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω)
            (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure +
          8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
            (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
              rw [hstartNormEq]
  have hOldLpBudget : lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma +
        144 * (900000 * M.gamma) *
          (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) +
            9 * (p : ℝ) / (3 ^ 16 : ℝ)) +
        8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
          (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := by
    calc
      _ = Gaussian.positiveLpNorm (Cutoff.cutoffSampleLaw M).toMeasure
            (p : ℝ) oldTrace := hOldEq'.symm
      _ ≤ lpNorm (fun ω => cirFamilyTrace (FamilyAt (n + 1)) 0 ω)
            (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure +
          8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
            (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50) := hOldBound
      _ ≤ _ := by nlinarith [hstartNorm]
  exact ⟨hOldMem, hOldLpBudget⟩

private theorem aoCir_restore_small_gamma_step
    (M : ABKModel 2) (m : ℤ) {p : ℕ} (hp12 : 12 ≤ p)
    (hγsmall : M.gamma ≤ 1 / 327680)
    (hOldMem : MemLp (fun ω => traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M (m - 8) : ℝ))
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure)
    (hOldLp : lpNorm (fun ω => traceDefect (cubeSet (originCube 2 m))
      (Cutoff.coefficientCutoff M.nu m ω).toFun (Annealed.sigmaBar M (m - 8) : ℝ))
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      700 * M.gamma + 144 * (900000 * M.gamma) *
        (3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) + 9 * (p : ℝ) / (3 ^ 16 : ℝ)) +
      8 * (107 / 12 : ℝ) * (p : ℝ) * (9 / 2 : ℝ) * M.gamma *
        (3 : ℝ) ^ (16 * M.gamma) * ((2.2 : ℝ) ^ 2 * 50)) :
    MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
  classical
  let n : ℤ := m - 8
  let root : TriadicCube 2 := originCube 2 m
  let oldTrace : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    traceDefect (cubeSet root) (Cutoff.coefficientCutoff M.nu m ω).toFun
      (Annealed.sigmaBar M n : ℝ)
  have hrestore (ω : Cutoff.CutoffSample 2) :
      cutoffTraceDefect M m m ω ≤ (1017 / 1000 : ℝ) * oldTrace ω + M.gamma := by
    simpa only [oldTrace, root, n, show m - 8 = n by rfl] using
      aoCir_eight_shell_frame_restore M m ω hγsmall
  have hDomMem : MemLp (fun ω => (1017 / 1000 : ℝ) * oldTrace ω + M.gamma)
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := by
    have hmuls := hOldMem.const_smul (1017 / 1000 : ℝ)
    have hadd := hmuls.add (memLp_const M.gamma)
    have heq : (fun ω => (1017 / 1000 : ℝ) * oldTrace ω + M.gamma) =
        (1017 / 1000 : ℝ) • oldTrace + (fun _ => M.gamma) := by
      funext ω
      rfl
    rw [heq]
    exact hadd
  have htargetMem : MemLp (cutoffTraceDefect M m m) (ENNReal.ofReal (p : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply hDomMem.mono'
    · exact (Variational.cutoffTraceDefect_measurable M m m).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (Variational.cutoffTraceDefect_nonneg M m m ω)]
        exact hrestore ω
  have hpOrd : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast (show 1 ≤ p by omega)
  have hDomLp : lpNorm (fun ω => (1017 / 1000 : ℝ) * oldTrace ω + M.gamma)
      (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure + M.gamma := by
    have hmulMem := hOldMem.const_smul (1017 / 1000 : ℝ)
    have htri := lpNorm_add_le (f := (1017 / 1000 : ℝ) • oldTrace)
      (g := fun _ => M.gamma) hmulMem hpOrd
    have hsum : (1017 / 1000 : ℝ) • oldTrace + (fun _ => M.gamma) =
        (fun ω => (1017 / 1000 : ℝ) * oldTrace ω + M.gamma) := by
      funext ω
      rfl
    rw [hsum] at htri
    have hscale : lpNorm ((1017 / 1000 : ℝ) • oldTrace) (ENNReal.ofReal (p : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure =
        (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
          (Cutoff.cutoffSampleLaw M).toMeasure := by
      rw [lpNorm_const_smul]
      norm_num
    have hpReal : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    have hconst : lpNorm (fun _ : Cutoff.CutoffSample 2 => M.gamma)
        (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure = M.gamma := by
      rw [lpNorm_const' (ENNReal.ofReal_ne_zero_iff.mpr hpReal)
        ENNReal.ofReal_ne_top]
      simp [Real.norm_of_nonneg M.shellPrefix.gamma_pos.le]
    rw [hscale, hconst] at htri
    exact htri
  have htargetLp : lpNorm (cutoffTraceDefect M m m) (ENNReal.ofReal (p : ℝ))
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
        (Cutoff.cutoffSampleLaw M).toMeasure + M.gamma := by
    calc
      _ ≤ lpNorm (fun ω => (1017 / 1000 : ℝ) * oldTrace ω + M.gamma)
          (ENNReal.ofReal (p : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure := by
        apply lpNorm_mono_real hDomMem
        intro ω
        rw [Real.norm_of_nonneg (Variational.cutoffTraceDefect_nonneg M m m ω)]
        exact hrestore ω
      _ ≤ _ := hDomLp
  have hstartCoeff : 3 * Real.sqrt ((p : ℝ) / (3 ^ 16 : ℝ)) =
      3 * Real.sqrt (p : ℝ) / 3 ^ 8 := by
    have hpow : (3 : ℝ) ^ 16 = ((3 : ℝ) ^ 8) ^ 2 := by norm_num
    rw [hpow, Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have hrecurrence :
      (1017 / 1000 : ℝ) *
        (700 * M.gamma + 144 * (900000 * M.gamma) *
          (3 * Real.sqrt (p : ℝ) / 3 ^ 8 + 9 * (p : ℝ) / 3 ^ 16) +
          (107 / 12) * (p : ℝ) * (9 / 2) * M.gamma * 8 *
            (3 : ℝ) ^ (16 * M.gamma) * (2.2 : ℝ) ^ 2 * 50) + M.gamma ≤
      (14 / 100 : ℝ) * (900000 * M.gamma * (p : ℝ)) := by
    exact aoCir_small_gamma_step_contraction M.shellPrefix.gamma_pos
      hγsmall (show 12 ≤ (p : ℝ) by exact_mod_cast hp12)
  have hcap : (14 / 100 : ℝ) * (900000 * M.gamma * (p : ℝ)) ≤
      900000 * M.gamma * (p : ℝ) := by
    have hp0 : 0 ≤ (p : ℝ) := by positivity
    nlinarith [M.shellPrefix.gamma_pos.le, hp0]
  refine ⟨?_, ?_⟩
  · simpa only [ENNReal.ofReal_natCast] using htargetMem
  · have hrestoreBudget :
        (1017 / 1000 : ℝ) * lpNorm oldTrace (ENNReal.ofReal (p : ℝ))
            (Cutoff.cutoffSampleLaw M).toMeasure + M.gamma ≤
          (1017 / 1000 : ℝ) *
            (700 * M.gamma + 144 * (900000 * M.gamma) *
              (3 * Real.sqrt (p : ℝ) / 3 ^ 8 + 9 * (p : ℝ) / 3 ^ 16) +
              (107 / 12) * (p : ℝ) * (9 / 2) * M.gamma * 8 *
                (3 : ℝ) ^ (16 * M.gamma) * (2.2 : ℝ) ^ 2 * 50) + M.gamma := by
      nlinarith [hOldLp, hstartCoeff]
    simpa only [ENNReal.ofReal_natCast] using
      htargetLp.trans (hrestoreBudget.trans (hrecurrence.trans hcap))

private theorem aoCir_small_gamma_step_bound_of_prev_caps
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ k : ℤ, nativeInductionState M h k)
    {m : ℤ} {p : ℕ} (hp12 : 12 ≤ p) (hpEven : Even p)
    (hpP : p ≤ smallGammaSeedP M.gamma)
    (hprev : ∀ q : ℕ, 12 ≤ q → Even q → q ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M (m - 8) (m - 8)) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M (m - 8) (m - 8)) (q : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (q : ℝ)) :
    MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
  have hstart := aoCir_start_average_bound_of_prev_caps M h hM hstate
    hp12 hpEven hpP hprev
  have hOld := aoCir_old_frame_trace_bound_of_start reset M h hM hγ hγsmall
    hstate hp12 hpP hstart
  exact aoCir_restore_small_gamma_step M m hp12 hγsmall hOld.1 hOld.2

private theorem aoCir_native_state_scalar_corridor
    (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hstate : nativeInductionState M h n) :
    M.nu ≤ (Annealed.sigmaBar M n : ℝ) ∧
      (Annealed.sigmaBar M n : ℝ) ^ 2 ≤
        M.nu ^ 2 + (13 / 8 : ℝ) * shellVarianceSum h M.gamma n := by
  exact ⟨hstate.2.2.2.2.2.1, hstate.2.2.2.2.2.2.2⟩

private theorem aoCir_small_gamma_finite_even_caps_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero)
    (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ n : ℤ, nativeInductionState M h n) :
    ∀ m : ℤ, ∀ p : ℕ, 12 ≤ p → Even p → p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
  have hseed := step_ao_cir_small_gamma_seed M h hM M.shellPrefix.gamma_pos hγsmall
    (fun n => aoCir_native_state_scalar_corridor M h n (hstate n))
  obtain ⟨mStar, hbase⟩ := hseed
  have hcapsNat : ∀ k : ℕ, ∀ p : ℕ, 12 ≤ p → Even p →
      p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M (mStar + k) (mStar + k)) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M (mStar + k) (mStar + k)) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hp12 hpEven hpP
        have hprev : ∀ q : ℕ, 12 ≤ q → Even q →
            q ≤ smallGammaSeedP M.gamma →
            MemLp (cutoffTraceDefect M (mStar + (k : ℤ) - 8) (mStar + (k : ℤ) - 8))
                (q : ℝ≥0∞) (Cutoff.cutoffSampleLaw M).toMeasure ∧
              lpNorm (cutoffTraceDefect M (mStar + (k : ℤ) - 8) (mStar + (k : ℤ) - 8))
                (q : ℝ≥0∞) (Cutoff.cutoffSampleLaw M).toMeasure ≤
                  900000 * M.gamma * (q : ℝ) := by
          intro q hq12 hqEven hqP
          by_cases hk : k < 8
          · have hlabel : mStar + (k : ℤ) - 8 ≤ mStar := by omega
            have hseeded := hbase (mStar + (k : ℤ) - 8) hlabel q hq12 hqEven hqP
            exact ⟨hseeded.1, hseeded.2.1.trans hseeded.2.2⟩
          · have hlabel : mStar + (k : ℤ) - 8 = mStar + ((k - 8 : ℕ) : ℤ) := by
              omega
            rw [hlabel]
            exact ih (k - 8) (by omega) q hq12 hqEven hqP
        exact aoCir_small_gamma_step_bound_of_prev_caps reset M h hM
          hγ hγsmall hstate hp12 hpEven hpP hprev
  have hcaps : ∀ m' : ℤ, ∀ p : ℕ, 12 ≤ p → Even p →
      p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M m' m') (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M m' m') (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
    intro m' p hp12 hpEven hpP
    by_cases hm' : m' ≤ mStar
    · have hseeded := hbase m' hm' p hp12 hpEven hpP
      exact ⟨hseeded.1, hseeded.2.1.trans hseeded.2.2⟩
    · have hgt : mStar < m' := lt_of_not_ge hm'
      have hgapNonneg : 0 ≤ m' - mStar := by omega
      let k : ℕ := (m' - mStar).toNat
      have hcast : (k : ℤ) = m' - mStar := by
        dsimp [k]
        exact Int.toNat_of_nonneg hgapNonneg
      have hlabel : m' = mStar + (k : ℤ) := by omega
      rw [hlabel]
      exact hcapsNat k p hp12 hpEven hpP
  exact hcaps

/-- The complete AO-CIR-FINITE-EVEN conclusion, conditional only on the
single reset producer. It includes the even-order induction, real-order
fill, and both seed-order gates. -/
theorem aoCir_finite_even_of_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : ∀ n : ℤ, nativeInductionState M h n) :
    (∀ p : ℕ, 12 ≤ p → Even p → p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ)) ∧
    (∀ p : ℝ, 1 ≤ p → p ≤ (smallGammaSeedP M.gamma : ℝ) →
      lpNorm (cutoffTraceDefect M m m) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
        2 * 900000 * M.gamma * p + 12 * 900000 * M.gamma) ∧
    M.gamma * (smallGammaSeedP M.gamma : ℝ) > 1 / 19000 ∧
      (48 : ℝ) ≤ 4 * (smallGammaSeedP M.gamma : ℝ) := by
  have hP20 : 20 ≤ smallGammaSeedP M.gamma := by
    unfold smallGammaSeedP
    exact le_max_left _ _
  have hPeven : Even (smallGammaSeedP M.gamma) := by
    unfold smallGammaSeedP
    by_cases hfloor : 20 ≤ 2 * ⌊(1 / 16384 : ℝ) / (2 * M.gamma)⌋₊
    · rw [max_eq_right hfloor]
      exact even_two_mul _
    · have hle : 2 * ⌊(1 / 16384 : ℝ) / (2 * M.gamma)⌋₊ ≤ 20 := by omega
      rw [max_eq_left hle]
      exact ⟨10, rfl⟩
  have hcaps : ∀ p : ℕ, 12 ≤ p → Even p → p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ) := by
    by_cases hsmall : M.gamma ≤ 1 / 327680
    · exact (aoCir_small_gamma_finite_even_caps_of_reset reset M h hM hγ hsmall hstate m)
    · intro p hp12 hpEven hpP
      have hlarge := aoCir_large_gamma_finite_even_caps M h
        (lt_of_not_ge hsmall) hγ m (hstate m)
      exact hlarge.2 p hp12 hpEven (by simpa only [hlarge.1] using hpP)
  have hfill : ∀ p : ℝ, 1 ≤ p → p ≤ (smallGammaSeedP M.gamma : ℝ) →
      lpNorm (cutoffTraceDefect M m m) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
        2 * 900000 * M.gamma * p + 12 * 900000 * M.gamma := by
    intro p hp hpP
    exact aoCir_real_order_fill_of_even_caps hP20 hPeven M.gamma
      M.shellPrefix.gamma_pos.le hcaps hp hpP
  have hgate := aoCir_small_gamma_seed_order_gates M.shellPrefix.gamma_pos
  exact ⟨hcaps, hfill, hgate.1, hgate.2⟩

/-- AO-CIR-FINITE-EVEN. The order-reset theorem is
instantiated internally, so the node exposes no producer premise. -/
theorem ao_cir_finite_even
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : ∀ n : ℤ, nativeInductionState M h n) :
    (∀ p : ℕ, 12 ≤ p → Even p → p ≤ smallGammaSeedP M.gamma →
      MemLp (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ∧
        lpNorm (cutoffTraceDefect M m m) (p : ℝ≥0∞)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ 900000 * M.gamma * (p : ℝ)) ∧
    (∀ p : ℝ, 1 ≤ p → p ≤ (smallGammaSeedP M.gamma : ℝ) →
      lpNorm (cutoffTraceDefect M m m) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
        2 * 900000 * M.gamma * p + 12 * 900000 * M.gamma) ∧
    M.gamma * (smallGammaSeedP M.gamma : ℝ) > 1 / 19000 ∧
      (48 : ℝ) ≤ 4 * (smallGammaSeedP M.gamma : ℝ) := by
  exact aoCir_finite_even_of_reset order_reset_producer
    M h hM hγ m hstate

end
end ASDExplicitGamma.AllOrder
