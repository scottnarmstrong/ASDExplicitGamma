module

public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.MultiplierMatrixBound
public import ASDExplicitGamma.Main.EnvelopeHMaxHistory
public import ASDExplicitGamma.Main.AffineMatrixMoments
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Cold.NativeLocalResponse
public import ASDExplicitGamma.Gaussian.RioTwoSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The source matrix estimate turns a max-based history envelope into the two
multiplier moments consumed by the OLD-frame generator.  The history carrier
is kept abstract so that this helper can be specialized to the corrected
max-based MA-ENVELOPE-H object. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
  ASDExplicitGamma.Inverse ASDExplicitGamma.Cold Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Homogenization.Book.Ch04
open Algsuperdiff.Section3.Provider.BadEvents

namespace ASDExplicitGamma.Main

/-- Analytic integration after deriving the source matrix inequality from
the actual coarse matrices and the max-based history. -/
private theorem multiplier_moments_of_aead_matrix_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (H_U M_U : Ω → ℝ) (Hcap : ℝ)
    (hH : MemLp H_U 2 μ)
    (hH_nonneg : 0 ≤ᵐ[μ] H_U)
    (hHcap : lpNorm H_U 2 μ ≤ Hcap)
    (hM_meas : AEStronglyMeasurable M_U μ)
    (hM_nonneg : 0 ≤ᵐ[μ] M_U)
    (hMatrix : ∀ᵐ ω ∂μ,
      M_U ω ≤ 1 + 2 * H_U ω + Real.sqrt (2 * H_U ω)) :
    ((((∫ ω, M_U ω ∂μ) ≤ mainM0 Hcap ∧
      (∫ ω, mainD * M_U ω * H_U ω ∂μ) ≤ mainD * mainM0 Hcap * Hcap) ∧
      lpNorm M_U 2 μ ≤ mainM0 Hcap) ∧ MemLp M_U 2 μ) ∧ 0 ≤ᵐ[μ] M_U := by
  have hHcap_nonneg : 0 ≤ Hcap := le_trans (lpNorm_nonneg (f := H_U) (p := 2) (μ := μ)) hHcap
  have hH_integrable : Integrable H_U μ := hH.integrable (by norm_num)
  let one : Ω → ℝ := fun _ => 1
  let Htwo : Ω → ℝ := fun ω => 2 * H_U ω
  let S : Ω → ℝ := fun ω => Real.sqrt (2 * H_U ω)
  let F : Ω → ℝ := one + (Htwo + S)
  have hOne : MemLp one 2 μ := memLp_const (1 : ℝ)
  have hH_lp : MemLp H_U (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hH
  have hOne_lp : MemLp one (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hOne
  have hOne_norm : lpNorm one 2 μ = 1 := by
    simp [one]
  have hHmean : (∫ ω, H_U ω ∂μ) ≤ Hcap := by
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
      hH_nonneg (Filter.Eventually.of_forall (fun _ => by norm_num)) hH_lp hOne_lp
    norm_num only [Real.rpow_ofNat] at hh
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
    have hNormH : Real.sqrt (∫ ω, H_U ω ^ 2 ∂μ) = lpNorm H_U 2 μ := by
      rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hH]
      exact Real.sqrt_sq (lpNorm_nonneg (f := H_U) (p := 2) (μ := μ))
    calc
      (∫ ω, H_U ω ∂μ) = ∫ ω, H_U ω * one ω ∂μ := by simp [one]
      _ ≤ _ := by simpa [one, hNormH, IsProbabilityMeasure.measure_univ] using hh
      _ ≤ Hcap := hHcap
  have hS_meas : AEStronglyMeasurable S μ := by
    exact Real.continuous_sqrt.comp_aestronglyMeasurable
      (hH.aestronglyMeasurable.const_mul 2)
  have hS_sq_integrable : Integrable (fun ω => S ω ^ 2) μ := by
    have hbase : Integrable (fun ω => 2 * H_U ω) μ := hH_integrable.const_mul 2
    apply hbase.congr
    filter_upwards [hH_nonneg] with ω hω
    simp only [S]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hω)]
  have hS : MemLp S 2 μ := (memLp_two_iff_integrable_sq hS_meas).2 hS_sq_integrable
  have hS_integral_sq : (∫ ω, S ω ^ 2 ∂μ) = 2 * ∫ ω, H_U ω ∂μ := by
    calc
      (∫ ω, S ω ^ 2 ∂μ) = ∫ ω, 2 * H_U ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hH_nonneg] with ω hω
        simp only [S]
        rw [Real.sq_sqrt (mul_nonneg (by norm_num) hω)]
      _ = 2 * ∫ ω, H_U ω ∂μ := by rw [integral_const_mul]
  have hSnorm_sq := ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hS
  have hS_cap : lpNorm S 2 μ ≤ Real.sqrt (2 * Hcap) := by
    apply (sq_le_sq₀ (lpNorm_nonneg (f := S) (p := 2) (μ := μ))
      (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Hcap), hSnorm_sq, hS_integral_sq]
    exact mul_le_mul_of_nonneg_left hHmean (by norm_num)
  have hHtwo : MemLp Htwo 2 μ := hH.const_mul 2
  have hHtwo_norm : lpNorm Htwo 2 μ = 2 * lpNorm H_U 2 μ := by
    rw [show Htwo = (2 : ℝ) • H_U by funext ω; simp [Htwo]]
    rw [lpNorm_const_smul]
    norm_num
  have hF : MemLp F 2 μ := by
    dsimp [F]
    exact hOne.add (hHtwo.add hS)
  have hFnorm : lpNorm F 2 μ ≤ mainM0 Hcap := by
    have hp : (1 : ENNReal) ≤ 2 := by norm_num
    have htriHS : lpNorm (Htwo + S) 2 μ ≤ lpNorm Htwo 2 μ + lpNorm S 2 μ :=
      lpNorm_add_le (f := Htwo) (g := S) hHtwo hp
    calc
      lpNorm F 2 μ ≤ lpNorm one 2 μ + lpNorm (Htwo + S) 2 μ := by
        simpa [F] using lpNorm_add_le hOne hp
      _ ≤ lpNorm one 2 μ + (lpNorm Htwo 2 μ + lpNorm S 2 μ) := by
        nlinarith [htriHS]
      _ ≤ 1 + 2 * Hcap + Real.sqrt (2 * Hcap) := by
        rw [hOne_norm, hHtwo_norm]
        have h := hS_cap
        nlinarith [hHcap]
      _ = mainM0 Hcap := by rfl
  have hF_nonneg : 0 ≤ᵐ[μ] F := by
    filter_upwards [hH_nonneg] with ω hω
    dsimp [F, one, Htwo, S]
    have hs := Real.sqrt_nonneg (2 * H_U ω)
    have ht : 0 ≤ 2 * H_U ω := mul_nonneg (by norm_num) hω
    linarith
  have hM_norm_le_F : ∀ᵐ ω ∂μ, ‖M_U ω‖ ≤ ‖F ω‖ := by
    filter_upwards [hM_nonneg, hMatrix, hF_nonneg] with ω hM hmat hFω
    rw [Real.norm_of_nonneg hM, Real.norm_of_nonneg hFω]
    change M_U ω ≤ 1 + 2 * H_U ω + Real.sqrt (2 * H_U ω) at hmat
    dsimp [F, one, Htwo, S]
    nlinarith [hmat]
  have hM : MemLp M_U 2 μ := hF.of_le hM_meas hM_norm_le_F
  have hM_lp : MemLp M_U (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hM
  have hMnorm : lpNorm M_U 2 μ ≤ mainM0 Hcap := by
    have hmono := eLpNorm_mono_ae (p := (2 : ENNReal)) hM_meas hM_norm_le_F
    have hMonoNorm : lpNorm M_U 2 μ ≤ lpNorm F 2 μ := by
      change (eLpNorm M_U 2 μ).toReal ≤ (eLpNorm F 2 μ).toReal
      exact ENNReal.toReal_mono hF.eLpNorm_ne_top hmono
    exact hMonoNorm.trans hFnorm
  have hM0_nonneg : 0 ≤ mainM0 Hcap := by
    unfold mainM0
    positivity
  have hM_integral_le : (∫ ω, M_U ω ∂μ) ≤ lpNorm M_U 2 μ := by
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
      hM_nonneg (Filter.Eventually.of_forall (fun _ => by norm_num)) hM_lp hOne_lp
    norm_num only [Real.rpow_ofNat] at hh
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
    have hNormM : Real.sqrt (∫ ω, M_U ω ^ 2 ∂μ) = lpNorm M_U 2 μ := by
      rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hM]
      exact Real.sqrt_sq (lpNorm_nonneg (f := M_U) (p := 2) (μ := μ))
    calc
      (∫ ω, M_U ω ∂μ) = ∫ ω, M_U ω * one ω ∂μ := by simp [one]
      _ ≤ _ := by simpa [one, hNormM, IsProbabilityMeasure.measure_univ] using hh
  have hHolderMH :
      (∫ ω, M_U ω * H_U ω ∂μ) ≤ lpNorm M_U 2 μ * lpNorm H_U 2 μ := by
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
      (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
      hM_nonneg hH_nonneg hM_lp hH_lp
    norm_num only [Real.rpow_ofNat] at hh
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
    have hNormM : Real.sqrt (∫ ω, M_U ω ^ 2 ∂μ) = lpNorm M_U 2 μ := by
      rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hM]
      exact Real.sqrt_sq (lpNorm_nonneg (f := M_U) (p := 2) (μ := μ))
    have hNormH : Real.sqrt (∫ ω, H_U ω ^ 2 ∂μ) = lpNorm H_U 2 μ := by
      rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hH]
      exact Real.sqrt_sq (lpNorm_nonneg (f := H_U) (p := 2) (μ := μ))
    simpa [hNormM, hNormH] using hh
  have hProduct : lpNorm M_U 2 μ * lpNorm H_U 2 μ ≤ mainM0 Hcap * Hcap :=
    mul_le_mul hMnorm hHcap (lpNorm_nonneg (f := H_U) (p := 2) (μ := μ)) hM0_nonneg
  have hD_nonneg : 0 ≤ mainD := by
    unfold mainD mainAlpha
    positivity
  have hMH_integrable : Integrable (fun ω => M_U ω * H_U ω) μ := hM.integrable_mul hH
  refine ⟨⟨⟨⟨hM_integral_le.trans hMnorm, ?_⟩, hMnorm⟩, hM⟩, hM_nonneg⟩
  · calc
      (∫ ω, mainD * M_U ω * H_U ω ∂μ) = mainD * ∫ ω, M_U ω * H_U ω ∂μ := by
        rw [show (fun ω => mainD * M_U ω * H_U ω) =
          (fun ω => mainD * (M_U ω * H_U ω)) by funext ω; ring, integral_const_mul]
      _ ≤ mainD * (lpNorm M_U 2 μ * lpNorm H_U 2 μ) :=
        mul_le_mul_of_nonneg_left hHolderMH hD_nonneg
      _ ≤ mainD * (mainM0 Hcap * Hcap) := mul_le_mul_of_nonneg_left hProduct hD_nonneg
      _ = mainD * mainM0 Hcap * Hcap := by ring

/-- The actual partial-insertion coefficient is locally uniformly elliptic at
every sample, as provided by its source entry bound. -/
private theorem main_partial_inserted_elliptic_on_cube
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    ∃ Λ, IsEllipticFieldOn M.nu Λ (cubeSet Q)
      (Model.partialInsertedCoefficient M m t ω).toFun := by
  have hCompact : IsCompact (closure (cubeSet Q)) :=
    (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨L, hL⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) hCompact
  have hCover : cubeSet Q ⊆ openCubeSet (originCube 2 L) := by
    intro x hx
    exact hL (subset_closure hx)
  refine ⟨(2 * 2 * Model.partialInsertedEntryBound M L m ω ^ 2 + M.nu ^ 2) / M.nu, ?_⟩
  exact Model.partialInsertedCoefficient_isEllipticFieldOn M L m ω ht
    (measurableSet_cubeSet Q) hCover

/-- A single normalized response norm is a.e.-measurable from the
restriction-law coarse-matrix observable and the true-frame identity. -/
private theorem main_partial_inserted_full_response_norm_aemeasurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (Q : TriadicCube 2) :
    AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
      fullResponseOperatorNorm Q
        ((Annealed.sigmaBar M m : ℝ)⁻¹ •
          (Model.partialInsertedCoefficient M m t ω).toFun))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := mainInsertionCoefficientLaw M m t
  have hP : RestrictionLawCarrier P := mainInsertionCoefficientLaw_lawCarrier M m t ht
  have hCoeff : AEMeasurable
      (fun a : RegCoeffField 2 => toFullBlockMat
        (coarseBlockMatrix (cubeSet Q) a.toFun)) P :=
    hP.aemeasurable_coarseFullBlockMatrix_cubeSet Q
  have hRaw : AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
      toFullBlockMat (coarseBlockMatrix (cubeSet Q)
        (Model.partialInsertedCoefficient M m t ω).toFun)) μ :=
    hCoeff.comp_aemeasurable
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable
  have hRawEntry (α β : BlockCoord 2) : AEMeasurable
      (fun ω : Cutoff.CutoffSample 2 =>
        toFullBlockMat (coarseBlockMatrix (cubeSet Q)
          (Model.partialInsertedCoefficient M m t ω).toFun) α β) μ :=
    (aemeasurable_pi_iff.mp (aemeasurable_pi_iff.mp hRaw α)) β
  let σ : ℝ := Annealed.sigmaBar M m
  have hFrame : AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
      toFullBlockMat (Variational.frameMatrix σ
        (coarseBlockMatrix (cubeSet Q)
          (Model.partialInsertedCoefficient M m t ω).toFun))) μ := by
    apply aemeasurable_pi_iff.mpr
    intro α
    apply aemeasurable_pi_iff.mpr
    intro β
    cases α with
    | inl i =>
      cases β with
      | inl j =>
        simpa [Variational.frameMatrix, toFullBlockMat, σ] using
          (hRawEntry (Sum.inl i) (Sum.inl j)).const_mul (σ⁻¹)
      | inr j =>
        simpa [Variational.frameMatrix, toFullBlockMat] using
          hRawEntry (Sum.inl i) (Sum.inr j)
    | inr i =>
      cases β with
      | inl j =>
        simpa [Variational.frameMatrix, toFullBlockMat] using
          hRawEntry (Sum.inr i) (Sum.inl j)
      | inr j =>
        simpa [Variational.frameMatrix, toFullBlockMat, σ] using
          (hRawEntry (Sum.inr i) (Sum.inr j)).const_mul σ
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  let L : FullBlockMat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
    { toFun := T
      map_add' := fun A B => map_add T A B
      map_smul' := fun c A => map_smul T c A }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hNorm : AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
      ‖L (toFullBlockMat (Variational.frameMatrix σ
        (coarseBlockMatrix (cubeSet Q)
          (Model.partialInsertedCoefficient M m t ω).toFun)))‖) μ :=
    hL.norm.measurable.comp_aemeasurable hFrame
  have heq : (fun ω : Cutoff.CutoffSample 2 =>
      fullResponseOperatorNorm Q
        ((Annealed.sigmaBar M m : ℝ)⁻¹ •
          (Model.partialInsertedCoefficient M m t ω).toFun)) =
      (fun ω => ‖L (toFullBlockMat (Variational.frameMatrix σ
        (coarseBlockMatrix (cubeSet Q)
          (Model.partialInsertedCoefficient M m t ω).toFun)))‖) := by
    funext ω
    obtain ⟨Λ, hEllω⟩ := main_partial_inserted_elliptic_on_cube M m t ht Q ω
    have hframe := congrArg toFullBlockMat
      (ASDExplicitGamma.Cold.cold_coarse_frame M.nu_pos hEllω
        (Annealed.sigmaBar_characterization M m).1)
    rw [fullResponseOperatorNorm, block_apply_opNorm_eq_full_matrix_opNorm]
    simpa [L, σ] using congrArg (fun A : FullBlockMat 2 =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖) hframe
  rw [heq]
  exact hNorm

/-- The max-based multiplier history on the actual partial-insertion carrier
is a.e.-measurable; this supplies no extra premise to its source moment theorem. -/
theorem main_partial_inserted_multiplier_history_aemeasurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    AEMeasurable (mainPartialInsertedMultiplierHistory M m t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q := originCube 2 (m - 5)
  have hDepth (j : ℕ) : AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
      mainPartialInsertedMultiplierDepthMax M m t ω j) μ := by
    let S := descendantsAtDepth Q j
    have hS : S.Nonempty := descendantsAtDepth_nonempty Q j
    have hcell (R : TriadicCube 2) (hR : R ∈ S) :
        AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
          fullResponseOperatorNorm R
            ((Annealed.sigmaBar M m : ℝ)⁻¹ •
              (Model.partialInsertedCoefficient M m t ω).toFun)) μ :=
      main_partial_inserted_full_response_norm_aemeasurable M m t ht R
    have heq : (fun ω : Cutoff.CutoffSample 2 =>
        mainPartialInsertedMultiplierDepthMax M m t ω j) =
        S.sup' hS (fun R ω => fullResponseOperatorNorm R
          ((Annealed.sigmaBar M m : ℝ)⁻¹ •
            (Model.partialInsertedCoefficient M m t ω).toFun)) := by
      funext ω
      change Book.Ch02.finsetSupReal S _ = _
      rw [Homogenization.Book.Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS]
      simp [Q, S]
    rw [heq]
    exact Homogenization.Book.Ch04.RestrictionLawCarrier.aemeasurable_finset_sup'
      hS (fun R hR => hcell R hR)
  change AEMeasurable (fun ω : Cutoff.CutoffSample 2 =>
    (1 - Scalar.inverseHistoryDiscount) * ∑' j : ℕ,
      Scalar.inverseHistoryDiscount ^ j *
        mainPartialInsertedMultiplierDepthMax M m t ω j) μ
  exact aemeasurable_const.mul (AEMeasurable.tsum (fun j =>
    aemeasurable_const.mul (hDepth j)))

/-- Fixed-time multiplier moments on the actual cutoff law.
The only envelope input is the intended max-based MA-ENVELOPE-H conclusion.
The matrix inequality is proved pathwise from VA-COARSE-DUALITY,
SC-ANALYTIC-BOUND-M, and the source's normalized geometric max history. -/
theorem main_multiplier_moments_of_max_history_envelope
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (Hcap : ℝ)
    (hHistoryFinite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainPartialInsertedTraceMaxHistory M m t ω < ⊤)
    (hH : MemLp
      (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hHcap : lpNorm
      (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hcap)
    :
    ((((∫ ω, mainPartialInsertedMultiplierHistory M m t ω ∂
      (Cutoff.cutoffSampleLaw M).toMeasure) ≤ mainM0 Hcap ∧
    (∫ ω, mainD * mainPartialInsertedMultiplierHistory M m t ω *
      (mainPartialInsertedTraceMaxHistory M m t ω).toReal ∂
        (Cutoff.cutoffSampleLaw M).toMeasure) ≤ mainD * mainM0 Hcap * Hcap) ∧
    lpNorm (fun ω => mainPartialInsertedMultiplierHistory M m t ω) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ mainM0 Hcap) ∧
    MemLp (mainPartialInsertedMultiplierHistory M m t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    0 ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      mainPartialInsertedMultiplierHistory M m t := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H_U : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (mainPartialInsertedTraceMaxHistory M m t ω).toReal
  let M_U : Cutoff.CutoffSample 2 → ℝ := mainPartialInsertedMultiplierHistory M m t
  have hHnonneg : 0 ≤ᵐ[μ] H_U := by
    filter_upwards with ω
    exact ENNReal.toReal_nonneg
  have hMnonneg : 0 ≤ᵐ[μ] M_U := by
    filter_upwards with ω
    exact main_partial_inserted_multiplier_history_nonneg M m t ω
  have hMatrix : ∀ᵐ ω ∂μ,
      M_U ω ≤ 1 + 2 * H_U ω + Real.sqrt (2 * H_U ω) := by
    filter_upwards [hHistoryFinite] with ω hfinite
    exact main_partial_inserted_multiplier_le_trace_history M m t ht ω hfinite
  have hM_meas' : AEStronglyMeasurable M_U μ := by
    exact (main_partial_inserted_multiplier_history_aemeasurable M m t ht).aestronglyMeasurable
  exact multiplier_moments_of_aead_matrix_bound H_U M_U Hcap hH
    hHnonneg hHcap hM_meas' hMnonneg hMatrix

/-- Multiplier moments with the corrected max-based ordinary
history envelope.  The deterministic matrix estimate is proved in the helper
above from the actual coarse matrix; the only history input is the exact
MA-ENVELOPE-H output for the same partial-insertion law and OLD frame. -/
theorem main_multiplier_moments_of_main_envelope_h
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((((∫ ω, mainPartialInsertedMultiplierHistory M m t ω ∂
      (Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainM0 (mainEnvelopeH (theta M) M.gamma t) ∧
    (∫ ω, mainD * mainPartialInsertedMultiplierHistory M m t ω *
      (mainPartialInsertedTraceMaxHistory M m t ω).toReal ∂
        (Cutoff.cutoffSampleLaw M).toMeasure) ≤
      mainD * mainM0 (mainEnvelopeH (theta M) M.gamma t) *
        mainEnvelopeH (theta M) M.gamma t) ∧
    lpNorm (fun ω => mainPartialInsertedMultiplierHistory M m t ω) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      mainM0 (mainEnvelopeH (theta M) M.gamma t)) ∧
    MemLp (mainPartialInsertedMultiplierHistory M m t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    0 ≤ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      mainPartialInsertedMultiplierHistory M m t := by
  have hEnvelope := main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH
    M h hM hgamma m hpast t ht0 ht1
  have hfinite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  have hmem : MemLp
      (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.2.1
  have hcap : lpNorm
      (fun ω => (mainPartialInsertedTraceMaxHistory M m t ω).toReal)
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      mainEnvelopeH (theta M) M.gamma t := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.2.2
  exact main_multiplier_moments_of_max_history_envelope M m t
    ⟨ht0, ht1⟩ (mainEnvelopeH (theta M) M.gamma t) hfinite hmem hcap

end ASDExplicitGamma.Main

end
