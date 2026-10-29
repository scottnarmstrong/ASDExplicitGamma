module

public import ASDExplicitGamma.Main.ELinearObsLPart
public import ASDExplicitGamma.Main.HotTopCovariancePathwise
public import ASDExplicitGamma.Main.ELinearCauchyExpectation
public import ASDExplicitGamma.Main.ObserverAvgTheta
public import ASDExplicitGamma.Main.ObserverParentGapPaired
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellEnergy

/-! The parent-gap weighted part (the `G`-weighted half-gain feedback) of the
`L` group at the observer root: its expectation is at most
`(mainFourLoadAG - 2 mainBe) * sqrt (2 xi)`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Component bound: square of a multiplier-history square root factor. -/
theorem g_part_carrier_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B Mu : Ω → ℝ)
    (hB : MemLp B 2 μ) (hMu : MemLp Mu 2 μ) (hB0 : ∀ ω, 0 ≤ B ω)
    (hMu0 : 0 ≤ᵐ[μ] Mu) (P : ℝ) (hP : 0 ≤ P) (hprod : (∫ ω, B ω * Mu ω ∂μ) ≤ P)
    (w : ℝ) :
    Integrable (fun ω => ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2) μ ∧
      (∫ ω, ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2 ∂μ) ≤ (Real.sqrt P + 1) ^ 2 * w ^ 2 := by
  have hBMint : Integrable (fun ω => B ω * Mu ω) μ := hB.integrable_mul hMu
  have hBM0 : 0 ≤ᵐ[μ] (fun ω => B ω * Mu ω) := by
    filter_upwards [hMu0] with ω hω
    exact mul_nonneg (hB0 ω) hω
  obtain ⟨sBMi, sBMb⟩ := main_sqrt_expectation_ae μ _ hBMint hBM0
  have hfun : Integrable (fun ω => (B ω * Mu ω + 2 * Real.sqrt (B ω * Mu ω) + 1) * w ^ 2) μ :=
    (((hBMint.add (sBMi.const_mul 2)).add (integrable_const (1 : ℝ))).mul_const _)
  have hae : (fun ω => ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2) =ᵐ[μ]
      (fun ω => (B ω * Mu ω + 2 * Real.sqrt (B ω * Mu ω) + 1) * w ^ 2) := by
    filter_upwards [hBM0] with ω hω
    have h1 := Real.sq_sqrt hω
    calc ((Real.sqrt (B ω * Mu ω) + 1) * w) ^ 2 =
        ((Real.sqrt (B ω * Mu ω)) ^ 2 + 2 * Real.sqrt (B ω * Mu ω) + 1) * w ^ 2 := by ring
      _ = _ := by rw [h1]
  refine ⟨hfun.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_mul_const]
  have hint : (∫ ω, (B ω * Mu ω + 2 * Real.sqrt (B ω * Mu ω) + 1) ∂μ) =
      (∫ ω, B ω * Mu ω ∂μ) + 2 * (∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) + 1 := by
    have e1 := integral_add hBMint (sBMi.const_mul 2)
    have e2 := integral_add (hBMint.add (sBMi.const_mul 2)) (integrable_const (1 : ℝ))
    simp only [Pi.add_apply] at e1 e2
    rw [e2, e1, integral_const_mul]
    simp
  rw [hint]
  have hs : (∫ ω, Real.sqrt (B ω * Mu ω) ∂μ) ≤ Real.sqrt P := sBMb.trans (Real.sqrt_le_sqrt hprod)
  have hPs : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  nlinarith [hs, hPs]

/-- Component bound: history carrier times a deterministic factor. -/
theorem g_part_history_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → ℝ) (hB : MemLp B 2 μ)
    (β : ℝ) (hβ : lpNorm B 2 μ ≤ β) (c w : ℝ) :
    Integrable (fun ω => (c * B ω * w) ^ 2) μ ∧
      (∫ ω, (c * B ω * w) ^ 2 ∂μ) ≤ (c * β) ^ 2 * w ^ 2 := by
  have hI := ((hB.integrable_sq).const_mul ((c * w) ^ 2))
  have heq : (fun ω => (c * B ω * w) ^ 2) = fun ω => (c * w) ^ 2 * B ω ^ 2 := by
    funext ω; ring
  rw [heq]
  refine ⟨hI, ?_⟩
  rw [integral_const_mul]
  have hsq : (∫ ω, B ω ^ 2 ∂μ) ≤ β ^ 2 := by
    rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hB]
    exact pow_le_pow_left₀ lpNorm_nonneg hβ 2
  calc (c * w) ^ 2 * ∫ ω, B ω ^ 2 ∂μ ≤ (c * w) ^ 2 * β ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = (c * β) ^ 2 * w ^ 2 := by ring

/-- Real-variable form of the pathwise cell bound. -/
theorem g_part_real_ineq (κ kd G Pp Pm Hh Rr Bc Mc Ωp Ωm α : ℝ)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ kd) (hG : 0 ≤ G) (hPp : 0 ≤ Pp) (hPm : 0 ≤ Pm)
    (hH : 0 ≤ Hh) (hR : 0 ≤ Rr) (hHB : Hh ≤ Bc) (hRM : Rr = Mc)
    (hΩp : 0 ≤ Ωp) (hΩm : 0 ≤ Ωm) (hα : 0 ≤ α) :
    2 * κ * G * (Real.sqrt Pp + α * Hh * Ωp) +
      2 * κ * G * (Real.sqrt Pm + (Real.sqrt (Hh * Rr) + 1) * Ωm) ≤
    2 * kd * (G * Real.sqrt Pp + G * (α * Bc * Ωp) + G * Real.sqrt Pm +
      G * ((Real.sqrt (Bc * Mc) + 1) * Ωm)) := by
  subst hRM
  have hBc : 0 ≤ Bc := hH.trans hHB
  have hsq : Real.sqrt (Hh * Rr) ≤ Real.sqrt (Bc * Rr) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hHB hR)
  have h1 : α * Hh * Ωp ≤ α * Bc * Ωp :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHB hα) hΩp
  have h2 : (Real.sqrt (Hh * Rr) + 1) * Ωm ≤ (Real.sqrt (Bc * Rr) + 1) * Ωm :=
    mul_le_mul_of_nonneg_right (by linarith) hΩm
  have a1 : 0 ≤ Real.sqrt Pp + α * Hh * Ωp :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg hα hH) hΩp)
  have a2 : 0 ≤ Real.sqrt Pm + (Real.sqrt (Hh * Rr) + 1) * Ωm :=
    add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (add_nonneg (Real.sqrt_nonneg _) zero_le_one) hΩm)
  have hkd : 0 ≤ kd := hκ0.trans hκ
  have e1 : 2 * κ * G * (Real.sqrt Pp + α * Hh * Ωp) ≤
      2 * kd * G * (Real.sqrt Pp + α * Bc * Ωp) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ (by norm_num)) hG)
      (by linarith) a1 (by positivity)
  have e2 : 2 * κ * G * (Real.sqrt Pm + (Real.sqrt (Hh * Rr) + 1) * Ωm) ≤
      2 * kd * G * (Real.sqrt Pm + (Real.sqrt (Bc * Rr) + 1) * Ωm) :=
    mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκ (by norm_num)) hG)
      (by linarith) a2 (by positivity)
  nlinarith [e1, e2]

/-- The final algebra of the `G`-weighted feedback bound. -/
theorem g_part_final_alg (ξ kd w v q op om β α' Cm : ℝ) (hξ : 0 ≤ ξ) (hkd : 0 ≤ kd)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hα' : 0 ≤ α') (hα'le : α' ≤ 63 / 50) (hβ : 0 ≤ β)
    (hop : 0 ≤ op) (hom : 0 ≤ om) (hC : 0 ≤ Cm) :
    2 * kd * (Real.sqrt (2 * ξ) * Real.sqrt (ξ / 2 * w) +
      Real.sqrt (2 * ξ) * Real.sqrt ((α' * β * op) ^ 2) +
      Real.sqrt (2 * ξ) * Real.sqrt (ξ / 2 * v) +
      Real.sqrt (2 * ξ) * Real.sqrt ((Cm * om) ^ 2)) ≤
    2 * kd * (Real.sqrt ξ * (Real.sqrt w + Real.sqrt v) / Real.sqrt 2 +
      (63 / 50) * β * op + Cm * om) * Real.sqrt (2 * ξ) := by
  have hs0 : 0 ≤ Real.sqrt (2 * ξ) := Real.sqrt_nonneg _
  have e0 : Real.sqrt (2 * ξ) * Real.sqrt (ξ / 2) = ξ := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * ξ * (ξ / 2) = ξ ^ 2 by ring]
    exact Real.sqrt_sq hξ
  have e0' : Real.sqrt ξ * Real.sqrt (2 * ξ) / Real.sqrt 2 = ξ := by
    have h2 : Real.sqrt (2 * ξ) = Real.sqrt 2 * Real.sqrt ξ := Real.sqrt_mul (by norm_num) _
    rw [h2]
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    exact Real.sq_sqrt hξ
  have e1 : Real.sqrt (ξ / 2 * w) = Real.sqrt (ξ / 2) * Real.sqrt w := Real.sqrt_mul (by positivity) _
  have e3 : Real.sqrt (ξ / 2 * v) = Real.sqrt (ξ / 2) * Real.sqrt v := Real.sqrt_mul (by positivity) _
  have e2 : Real.sqrt ((α' * β * op) ^ 2) = α' * β * op :=
    Real.sqrt_sq (mul_nonneg (mul_nonneg hα' hβ) hop)
  have e4 : Real.sqrt ((Cm * om) ^ 2) = Cm * om := Real.sqrt_sq (mul_nonneg hC hom)
  rw [e1, e2, e3, e4]
  have lhs : Real.sqrt (2 * ξ) * (Real.sqrt (ξ / 2) * Real.sqrt w) +
      Real.sqrt (2 * ξ) * (α' * β * op) +
      Real.sqrt (2 * ξ) * (Real.sqrt (ξ / 2) * Real.sqrt v) +
      Real.sqrt (2 * ξ) * (Cm * om) =
      ξ * Real.sqrt w + ξ * Real.sqrt v + Real.sqrt (2 * ξ) * (α' * β * op) +
        Real.sqrt (2 * ξ) * (Cm * om) := by
    have := e0
    linear_combination (Real.sqrt w + Real.sqrt v) * this
  have rhs : (Real.sqrt ξ * (Real.sqrt w + Real.sqrt v) / Real.sqrt 2 +
      (63 / 50) * β * op + Cm * om) * Real.sqrt (2 * ξ) =
      ξ * Real.sqrt w + ξ * Real.sqrt v + Real.sqrt (2 * ξ) * ((63 / 50) * β * op) +
        Real.sqrt (2 * ξ) * (Cm * om) := by
    have := e0'
    linear_combination (Real.sqrt w + Real.sqrt v) * this
  have hmono : Real.sqrt (2 * ξ) * (α' * β * op) ≤ Real.sqrt (2 * ξ) * ((63 / 50) * β * op) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hα'le hβ) hop) hs0
  rw [lhs, mul_assoc (2 * kd) _ (Real.sqrt (2 * ξ)), rhs]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem main_e_linear_obs_G_part_expectation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (hobs_pos : 1 ≤ hobs) (hobs40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Gbar2 : CutoffSample 2 → ℝ, Integrable Gbar2 μ ∧ 0 ≤ᵐ[μ] Gbar2 ∧
      (∀ᵐ ω ∂μ, mainELinearObsGAverageTerm M (originCube 2 (m + (hobs : ℤ))) (5 + hobs)
        m t b L ω ≤ Gbar2 ω) ∧
      (∫ ω, Gbar2 ω ∂μ) ≤
        (mainFourLoadAG (b ^ 2) (mainEnvelopeH (theta M) M.gamma t)
          (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q -
          2 * mainBe (b ^ 2) q) *
        mainG (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) := by
  intro μ b L q
  classical
  let Q := originCube 2 (m + (hobs : ℤ))
  let d := 5 + hobs
  let S := descendantsAtDepth Q d
  have hpast' : ∀ n ≤ m, nativeInductionState M h n :=
    fun n hn => hpast n (lt_of_le_of_lt hn hm)
  have hq : oldSignedFlatBoundaryEnergy Q b L ≤ b ^ 2 * q :=
    main_affine_flat_boundary_cap M h hM m hobs hobs_pos hobs40
  have hbpos : 0 < b := by
    have hh := hM.1
    have hs := (Annealed.sigmaBar_characterization M m).1
    unfold b q3ModelAmplitude
    exact div_pos (mul_pos hh (Real.rpow_pos_of_pos (by norm_num) _)) hs
  have hrQ : cubeScaleFactor Q / (3 : ℝ) ^ d ≤ (3 : ℝ) ^ (-6 : ℤ) * L.1 := by
    unfold cubeScaleFactor
    change (3 : ℝ) ^ (m + (hobs : ℤ)) / (3 : ℝ) ^ (5 + hobs) ≤
      (3 : ℝ) ^ (-6 : ℤ) * (3 : ℝ) ^ (m + 1)
    rw [← zpow_add₀ (by norm_num)]
    have : (3 : ℝ) ^ (m + (hobs : ℤ)) / (3 : ℝ) ^ (5 + hobs) = (3 : ℝ) ^ (m - 5) := by
      rw [← zpow_natCast, ← zpow_sub₀ (by norm_num)]
      congr 1
      push_cast
      ring
    rw [this]
    exact le_of_eq (by congr 1; omega)
  have hscaleU : ∀ U ∈ S, U.scale = m - 5 := by
    intro U hU
    have hh := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale = (m + (hobs : ℤ)) - ((5 + hobs : ℕ) : ℤ) at hh
    omega
  have hκ : ∀ U ∈ S, oldSignedDerivativeKappa (cubeScaleFactor U) b L.1 ≤ mainKd (b ^ 2) := by
    intro U hU
    apply old_signed_derivative_kappa_le_mainKd _ _ _ (by unfold cubeScaleFactor; positivity)
    have hs : U.scale = m - 5 := hscaleU U hU
    unfold cubeScaleFactor
    rw [hs]
    change (3 : ℝ) ^ (m - 5) ≤ (3 : ℝ) ^ (-6 : ℤ) * (3 : ℝ) ^ (m + 1)
    rw [← zpow_add₀ (by norm_num)]
    exact le_of_eq (by congr 1; omega)
  let xi := mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t
  let H := mainEnvelopeH (theta M) M.gamma t
  have hHnn : 0 ≤ H := by unfold H mainEnvelopeH; exact sq_nonneg _
  have hM0nn : 0 ≤ mainM0 H := by unfold mainM0; positivity
  obtain ⟨hΘint, hΘle⟩ := observer_avg_theta_row M h hM hγ N hpast m hm t ht hobs hobs40
  have hpair := fun ω => observer_parent_paired_le_two_avg_theta M hγ m t ht hobs hobs40 ω
  have hcardpos : 0 < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q d)
  have hdA : ∀ F : TriadicCube 2 → ℝ, descendantsAverage Q d F = finAvg S F := fun F => rfl
  have hΘ0 : ∀ ω, 0 ≤ descendantsAverage Q d (fun U => mixedOldTheta M m U t ω) := by
    intro ω
    have h1 : 0 ≤ descendantsAverage Q d (fun U =>
        oldSignedPrimalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω) ^ 2 +
        oldSignedReciprocalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω) ^ 2) := by
      unfold descendantsAverage
      exact mul_nonneg (inv_nonneg.mpr hcardpos.le)
        (Finset.sum_nonneg (fun U _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    have := hpair ω
    linarith
  have hxinn : 0 ≤ xi := by
    have h0 : 0 ≤ ∫ ω, descendantsAverage Q d (fun U => mixedOldTheta M m U t ω) ∂μ :=
      integral_nonneg hΘ0
    exact h0.trans hΘle
  let X : CutoffSample 2 → ℝ := fun ω => 2 * descendantsAverage Q d
    (fun U => mixedOldTheta M m U t ω)
  have hXint : Integrable X μ := hΘint.const_mul 2
  have hX0 : 0 ≤ᵐ[μ] X := Filter.Eventually.of_forall (fun ω => mul_nonneg (by norm_num) (hΘ0 ω))
  have hXa : (∫ ω, X ω ∂μ) ≤ 2 * xi := by
    unfold X
    rw [integral_const_mul]
    linarith
  -- deterministic profile averages
  have hOp0 : 0 ≤ mainOp (b ^ 2) := by unfold mainOp; positivity
  have hOm0 : 0 ≤ mainOm (b ^ 2) := by unfold mainOm; positivity
  have hOp : finAvg S (fun U => oldSignedFlatOscillationSize Q U b L true ^ 2) ≤
      mainOp (b ^ 2) ^ 2 :=
    main_oldSignedFlatPlus_descendant_average_le_mainOp_sq_scale Q d b hbpos L hrQ
  have hOm : finAvg S (fun U => oldSignedFlatOscillationSize Q U b L false ^ 2) ≤
      mainOm (b ^ 2) ^ 2 :=
    main_oldSignedFlatMinus_descendant_average_le_mainOm_sq_scale Q d b hbpos L hrQ
  have hpartP : finAvg S (fun U => oldSignedFlatL2Size Q U b L true ^ 2) =
      oldSignedFlatL2Size Q Q b L true ^ 2 :=
    old_signed_flat_l2_size_partition Q d b L true
  have hpartM : finAvg S (fun U => oldSignedFlatL2Size Q U b L false ^ 2) =
      oldSignedFlatL2Size Q Q b L false ^ 2 :=
    old_signed_flat_l2_size_partition Q d b L false
  have hl2m : oldSignedFlatL2Size Q Q b L false ^ 2 ≤ |b| ^ 2 := by
    rw [sq_abs]; exact main_flat_l2_minus_root_sq_le Q b L
  have hl2p : oldSignedFlatL2Size Q Q b L true ^ 2 ≤ b ^ 2 + b ^ 2 * q / 2 := by
    rw [main_flat_l2_plus_root_sq_eq]
    linarith
  have hmeanP : finAvg S (fun U => oldSignedFlatMeanSize Q U b L true ^ 2) ≤
      b ^ 2 + b ^ 2 * q / 2 := by
    refine (finAvg_mono S _ (fun U => oldSignedFlatL2Size Q U b L true ^ 2) ?_).trans
      (hpartP ▸ hl2p)
    intro U hU
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (old_signed_flat_mean_size_le_l2 Q d b L true U hU) 2
  have hmeanM : finAvg S (fun U => oldSignedFlatMeanSize Q U b L false ^ 2) ≤ |b| ^ 2 := by
    refine (finAvg_mono S _ (fun U => oldSignedFlatL2Size Q U b L false ^ 2) ?_).trans
      (hpartM ▸ hl2m)
    intro U hU
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (old_signed_flat_mean_size_le_l2 Q d b L false U hU) 2
  -- carriers and payments
  choose! Bc Muc hB0 hMu0 hBmem hBcap hMumem hMucap hprod hae using fun U (hU : U ∈ S) =>
    main_e_linear_obs_history_carriers M h hM hγ m hpast' t ht U (hscaleU U hU)
  have hpayP := fun U (hU : U ∈ S) => main_e_linear_obs_mean_proxy_payment M h hM hγ N hpast m hm t ht
    Q d U hU (hscaleU U hU) b L true
  have hpayM := fun U (hU : U ∈ S) => main_e_linear_obs_mean_proxy_payment M h hM hγ N hpast m hm t ht
    Q d U hU (hscaleU U hU) b L false
  let σ : ℝ := (Annealed.sigmaBar M m : ℝ)
  let Gf : TriadicCube 2 → CutoffSample 2 → ℝ := fun U ω =>
    oldSignedReciprocalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (mainELinearObsCoefficient Q m t ω)
  have hG0 : ∀ U ω, 0 ≤ Gf U ω := fun U ω => Real.sqrt_nonneg _
  have hGX : ∀ᵐ ω ∂μ, finAvg S (fun U => Gf U ω ^ 2) ≤ X ω := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have h1 := hpair ω
    refine le_trans ?_ h1
    rw [hdA]
    exact finAvg_mono S _ _ (fun U _ => le_add_of_nonneg_left (sq_nonneg _))
  let α' : ℝ := 1 / 2 + inverseHistoryDiscount
  have hα' : 0 ≤ α' := by
    have := inverse_history_discount_range.1
    unfold α'; linarith
  have hα'le : α' ≤ 63 / 50 := by
    have := inverseHistoryDiscount_le
    unfold α'; linarith
  -- component 1 and 3: square roots of the directional mean proxies
  have comp_proxy : ∀ plus : Bool, ∀ c0 : ℝ,
      finAvg S (fun U => oldSignedFlatMeanSize Q U b L plus ^ 2) ≤ c0 →
      ∃ Gb : CutoffSample 2 → ℝ, Integrable Gb μ ∧ 0 ≤ᵐ[μ] Gb ∧
        (∀ᵐ ω ∂μ, finAvg S (fun U => Gf U ω *
          Real.sqrt (mainELinearObsMeanProxy M m t Q U b L plus ω)) ≤ Gb ω) ∧
        (∫ ω, Gb ω ∂μ) ≤ Real.sqrt (2 * xi) * Real.sqrt (xi / 2 * c0) := by
    intro plus c0 hc0
    have hpay := fun U (hU : U ∈ S) => main_e_linear_obs_mean_proxy_payment M h hM hγ N hpast m hm t ht
      Q d U hU (hscaleU U hU) b L plus
    refine main_weighted_cell_majorant μ S Gf
      (fun U ω => Real.sqrt (mainELinearObsMeanProxy M m t Q U b L plus ω)) X (2 * xi)
      (xi / 2 * c0) hXint hX0 hXa hGX ?_ ?_ hG0
    · intro U hU
      refine (hpay U hU).1.congr (Filter.Eventually.of_forall (fun ω => ?_))
      exact (Real.sq_sqrt (mainELinearObsMeanProxy_nonneg M m t Q U b L plus ω)).symm
    · have h1 : ∀ U ∈ S, (∫ ω, Real.sqrt (mainELinearObsMeanProxy M m t Q U b L plus ω) ^ 2 ∂μ) ≤
          xi / 2 * oldSignedFlatMeanSize Q U b L plus ^ 2 := by
        intro U hU
        have : (∫ ω, Real.sqrt (mainELinearObsMeanProxy M m t Q U b L plus ω) ^ 2 ∂μ) =
            ∫ ω, mainELinearObsMeanProxy M m t Q U b L plus ω ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ω =>
            Real.sq_sqrt (mainELinearObsMeanProxy_nonneg M m t Q U b L plus ω))
        rw [this]
        exact (hpay U hU).2.1
      refine (finAvg_mono S _ _ h1).trans ?_
      rw [finAvg_mul_left]
      exact mul_le_mul_of_nonneg_left hc0 (by positivity)
  -- component 2: history times plus oscillation
  have comp2 : ∃ Gb : CutoffSample 2 → ℝ, Integrable Gb μ ∧ 0 ≤ᵐ[μ] Gb ∧
      (∀ᵐ ω ∂μ, finAvg S (fun U => Gf U ω *
        (α' * Bc U ω * oldSignedFlatOscillationSize Q U b L true)) ≤ Gb ω) ∧
      (∫ ω, Gb ω ∂μ) ≤ Real.sqrt (2 * xi) * Real.sqrt ((α' * mainBeta * mainOp (b ^ 2)) ^ 2) := by
    refine main_weighted_cell_majorant μ S Gf
      (fun U ω => α' * Bc U ω * oldSignedFlatOscillationSize Q U b L true) X (2 * xi)
      ((α' * mainBeta * mainOp (b ^ 2)) ^ 2) hXint hX0 hXa hGX
      (fun U hU => (g_part_history_sq μ (Bc U) (hBmem U hU) mainBeta (hBcap U hU) α'
        (oldSignedFlatOscillationSize Q U b L true)).1) ?_ hG0
    have h1 : ∀ U ∈ S, (∫ ω, (α' * Bc U ω * oldSignedFlatOscillationSize Q U b L true) ^ 2 ∂μ) ≤
        (α' * mainBeta) ^ 2 * (oldSignedFlatOscillationSize Q U b L true ^ 2) :=
      fun U hU => (g_part_history_sq μ (Bc U) (hBmem U hU) mainBeta (hBcap U hU) α'
        (oldSignedFlatOscillationSize Q U b L true)).2
    refine (finAvg_mono S _ _ h1).trans ?_
    rw [finAvg_mul_left]
    calc (α' * mainBeta) ^ 2 * finAvg S (fun U => oldSignedFlatOscillationSize Q U b L true ^ 2)
        ≤ (α' * mainBeta) ^ 2 * mainOp (b ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hOp (sq_nonneg _)
      _ = (α' * mainBeta * mainOp (b ^ 2)) ^ 2 := by ring
  -- component 4: multiplier-history square root times minus oscillation
  have hbmsq : Real.sqrt (mainBeta * mainM0 H) = mainBm H := rfl
  have hP0 : 0 ≤ mainBeta * mainM0 H := by unfold mainBeta; positivity
  have comp4 : ∃ Gb : CutoffSample 2 → ℝ, Integrable Gb μ ∧ 0 ≤ᵐ[μ] Gb ∧
      (∀ᵐ ω ∂μ, finAvg S (fun U => Gf U ω *
        ((Real.sqrt (Bc U ω * Muc U ω) + 1) * oldSignedFlatOscillationSize Q U b L false)) ≤ Gb ω) ∧
      (∫ ω, Gb ω ∂μ) ≤ Real.sqrt (2 * xi) * Real.sqrt (((mainBm H + 1) * mainOm (b ^ 2)) ^ 2) := by
    have hc4 := fun U (hU : U ∈ S) => g_part_carrier_sq μ (Bc U) (Muc U) (hBmem U hU)
      (hMumem U hU) (hB0 U hU) (hMu0 U hU) (mainBeta * mainM0 H) hP0 (hprod U hU)
      (oldSignedFlatOscillationSize Q U b L false)
    refine main_weighted_cell_majorant μ S Gf
      (fun U ω => (Real.sqrt (Bc U ω * Muc U ω) + 1) * oldSignedFlatOscillationSize Q U b L false)
      X (2 * xi) (((mainBm H + 1) * mainOm (b ^ 2)) ^ 2) hXint hX0 hXa hGX
      (fun U hU => (hc4 U hU).1) ?_ hG0
    have h1 : ∀ U ∈ S, (∫ ω, ((Real.sqrt (Bc U ω * Muc U ω) + 1) *
          oldSignedFlatOscillationSize Q U b L false) ^ 2 ∂μ) ≤
        (mainBm H + 1) ^ 2 * (oldSignedFlatOscillationSize Q U b L false ^ 2) := by
      intro U hU
      have := (hc4 U hU).2
      rw [hbmsq] at this
      exact this
    refine (finAvg_mono S _ _ h1).trans ?_
    rw [finAvg_mul_left]
    calc (mainBm H + 1) ^ 2 * finAvg S (fun U => oldSignedFlatOscillationSize Q U b L false ^ 2)
        ≤ (mainBm H + 1) ^ 2 * mainOm (b ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hOm (sq_nonneg _)
      _ = ((mainBm H + 1) * mainOm (b ^ 2)) ^ 2 := by ring
  obtain ⟨Gb1, i1, n1, p1, e1⟩ := comp_proxy true (b ^ 2 + b ^ 2 * q / 2) hmeanP
  obtain ⟨Gb3, i3, n3, p3, e3⟩ := comp_proxy false (b ^ 2) (by rw [← sq_abs b]; exact hmeanM)
  obtain ⟨Gb2, i2, n2, p2, e2⟩ := comp2
  obtain ⟨Gb4, i4, n4, p4, e4⟩ := comp4
  let kd := mainKd (b ^ 2)
  have hkd : 0 ≤ kd := mainKd_nonneg _
  have hq1 : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  refine ⟨fun ω => 2 * kd * (Gb1 ω + Gb2 ω + Gb3 ω + Gb4 ω),
    (((i1.add i2).add i3).add i4).const_mul _, ?_, ?_, ?_⟩
  · filter_upwards [n1, n2, n3, n4] with ω a1 a2 a3 a4
    have : 0 ≤ Gb1 ω + Gb2 ω + Gb3 ω + Gb4 ω := by
      have := a1; have := a2; have := a3; have := a4
      simp only [Pi.zero_apply] at *
      linarith
    exact mul_nonneg (mul_nonneg (by norm_num) hkd) this
  · filter_upwards [(Filter.eventually_all_finset S).2 (fun U hU => hae U hU), p1, p2, p3, p4]
      with ω hω q1 q2 q3 q4
    unfold mainELinearObsGAverageTerm
    have hcell : ∀ U ∈ S, mainELinearObsGCellTerm M m t b L Q U ω ≤
        2 * kd * (Gf U ω * Real.sqrt (mainELinearObsMeanProxy M m t Q U b L true ω) +
          Gf U ω * (α' * Bc U ω * oldSignedFlatOscillationSize Q U b L true) +
          Gf U ω * Real.sqrt (mainELinearObsMeanProxy M m t Q U b L false ω) +
          Gf U ω * ((Real.sqrt (Bc U ω * Muc U ω) + 1) *
            oldSignedFlatOscillationSize Q U b L false)) := by
      intro U hU
      obtain ⟨hinv, hresp⟩ := hω U hU
      have hinv0 := ASDExplicitGamma.Variational.lemmaVInverseHistory_nonneg U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t U ω)) hq1
      have hresp0 : 0 ≤ oldSignedResponseHistory U (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)) :=
        ENNReal.toReal_nonneg
      unfold mainELinearObsGCellTerm
      exact g_part_real_ineq (oldSignedDerivativeKappa (cubeScaleFactor U) b L.1) kd
        (Gf U ω) _ _ _ _ _ _ _ _ _
        (old_signed_q1_derivative_kappa_nonneg _ _ _ (by unfold cubeScaleFactor; positivity))
        (hκ U hU) (hG0 U ω) (mainELinearObsMeanProxy_nonneg M m t Q U b L true ω)
        (mainELinearObsMeanProxy_nonneg M m t Q U b L false ω) hinv0 hresp0 hinv hresp
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by
          have := inverse_history_discount_range.1
          linarith)
    refine (finAvg_mono S _ _ hcell).trans ?_
    rw [finAvg_mul_left, finAvg_add, finAvg_add, finAvg_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by norm_num) hkd)
  · have hint : (∫ ω, 2 * kd * (Gb1 ω + Gb2 ω + Gb3 ω + Gb4 ω) ∂μ) =
        2 * kd * ((∫ ω, Gb1 ω ∂μ) + (∫ ω, Gb2 ω ∂μ) + (∫ ω, Gb3 ω ∂μ) + (∫ ω, Gb4 ω ∂μ)) := by
      rw [integral_const_mul]
      congr 1
      have j12 := i1.add i2
      have j123 := j12.add i3
      have e12 := integral_add i1 i2
      have e123 := integral_add j12 i3
      have e1234 := integral_add j123 i4
      simp only [Pi.add_apply] at e12 e123 e1234
      rw [e1234, e123, e12]
    rw [hint]
    have hsum := add_le_add (add_le_add (add_le_add e1 e2) e3) e4
    refine (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hkd)).trans ?_
    have hw : 0 ≤ b ^ 2 + b ^ 2 * q / 2 := by
      have := mainAffineFlatBoundaryCapQ_nonneg (hobs - 1)
      positivity
    have halg := g_part_final_alg xi kd (b ^ 2 + b ^ 2 * q / 2) (b ^ 2) q (mainOp (b ^ 2))
      (mainOm (b ^ 2)) mainBeta α' (mainBm H + 1) hxinn hkd hw (sq_nonneg b) hα' hα'le
      (by norm_num [mainBeta]) hOp0 hOm0 (by unfold mainBm; positivity)
    refine halg.trans (le_of_eq ?_)
    unfold mainFourLoadAG mainG mainT0 mainC
    ring

end
end ASDExplicitGamma.Main
