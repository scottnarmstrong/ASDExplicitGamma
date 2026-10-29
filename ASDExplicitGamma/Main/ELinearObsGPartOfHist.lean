module

public import ASDExplicitGamma.Main.ELinearObsGPart
public import ASDExplicitGamma.Main.ELinearObsCellOfHist

/-! Successors of `ELinearObsGPart` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Successor of `main_e_linear_obs_G_part_expectation` with the history envelope `Hfun`. -/
theorem main_e_linear_obs_G_part_expectation_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (hobs_pos : 1 ≤ hobs) (hobs40 : hobs ≤ 40)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)
    let L := q3ModelLength (m + 1)
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    ∃ Gbar2 : CutoffSample 2 → ℝ, Integrable Gbar2 μ ∧ 0 ≤ᵐ[μ] Gbar2 ∧
      (∀ᵐ ω ∂μ, mainELinearObsGAverageTerm M (originCube 2 (m + (hobs : ℤ))) (5 + hobs)
        m t b L ω ≤ Gbar2 ω) ∧
      (∫ ω, Gbar2 ω ∂μ) ≤
        (mainFourLoadAG (b ^ 2) (Hfun t)
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
  let H := Hfun t
  have hHnn : 0 ≤ H := by exact le_trans lpNorm_nonneg (hHist t ht).2.2
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
    main_e_linear_obs_history_carriers_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ m hpast' t ht U (hscaleU U hU)
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
end
