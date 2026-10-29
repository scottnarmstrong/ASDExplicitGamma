module

public import ASDExplicitGamma.Main.ELinearObsLPart
public import ASDExplicitGamma.Main.ELinearObsCellExpectationOfHist

/-! Successors of `ELinearObsLPart` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Successor of `main_e_linear_obs_L_part_expectation` with the history envelope `Hfun`. -/
theorem main_e_linear_obs_L_part_expectation_ofHist
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
    ∃ Lbar : CutoffSample 2 → ℝ, Integrable Lbar μ ∧ 0 ≤ᵐ[μ] Lbar ∧
      (∀ᵐ ω ∂μ, mainELinearObsLAverageTerm M (originCube 2 (m + (hobs : ℤ))) (5 + hobs) m t b L ω ≤ Lbar ω) ∧
      (∫ ω, Lbar ω ∂μ) ≤ mainLinearError (b ^ 2) (Hfun t)
        (mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t) q := by
  intro μ b L q
  let Q := originCube 2 (m + (hobs : ℤ))
  let d := 5 + hobs
  let S := descendantsAtDepth Q d
  have hq : oldSignedFlatBoundaryEnergy Q b L ≤ b ^ 2 * q :=
    main_affine_flat_boundary_cap M h hM m hobs hobs_pos hobs40
  have hL : L = q3ModelLength (m + 1) := rfl
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
    have hs : U.scale = m - 5 := by
      have hh := scale_eq_sub_of_mem_descendantsAtDepth hU
      change U.scale = (m + (hobs : ℤ)) - ((5 + hobs : ℕ) : ℤ) at hh
      omega
    unfold cubeScaleFactor
    rw [hs]
    change (3 : ℝ) ^ (m - 5) ≤ (3 : ℝ) ^ (-6 : ℤ) * (3 : ℝ) ^ (m + 1)
    rw [← zpow_add₀ (by norm_num)]
    exact le_of_eq (by congr 1; omega)
  choose! A hAint hA0 hAle hAbound using fun U (hU : U ∈ S) =>
    main_e_linear_obs_L_cell_expectation_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm t ht b L Q d U hU
      (hscaleU U hU) (hκ U hU)
  let Lbar : CutoffSample 2 → ℝ := fun ω => ((S.card : ℝ)⁻¹) * ∑ U ∈ S, A U ω
  have hInt : Integrable Lbar μ :=
    (integrable_finset_sum S fun U hU => hAint U hU).const_mul _
  have hNN : 0 ≤ᵐ[μ] Lbar := by
    filter_upwards [(Filter.eventually_all_finset S).2 (fun U hU => hA0 U hU)] with ω hω
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun U hU => hω U hU))
  have hLe : ∀ᵐ ω ∂μ, mainELinearObsLAverageTerm M (originCube 2 (m + (hobs : ℤ))) (5 + hobs) m t b L ω ≤ Lbar ω := by
    filter_upwards [(Filter.eventually_all_finset S).2 (fun U hU => hAle U hU)] with ω hω
    exact finAvg_mono S _ _ (fun U hU => hω U hU)
  refine ⟨Lbar, hInt, hNN, hLe, ?_⟩
  -- the deterministic profile
  have hxi : True := trivial
  let xi := mainEnvelopeXi (b ^ 2) M.gamma mainSourceInversePrefix (theta M) t
  let H := Hfun t
  have hcell : (∫ ω, Lbar ω ∂μ) ≤ finAvg S (fun U => mainELinearObsLCellBound_ofHist (Hfun := Hfun) M h m t b L Q U) := by
    have hI : (∫ ω, Lbar ω ∂μ) = ((S.card : ℝ)⁻¹) * ∑ U ∈ S, ∫ ω, A U ω ∂μ := by
      simp only [Lbar]
      rw [integral_const_mul, integral_finset_sum S (fun U hU => hAint U hU)]
    rw [hI]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun U hU => hAbound U hU))
      (by positivity)
  refine hcell.trans ?_
  have hHnn : 0 ≤ H := by
    exact le_trans lpNorm_nonneg (hHist t ht).2.2
  have hM0nn : 0 ≤ mainM0 H := by
    unfold mainM0; positivity
  have hDnn : 0 ≤ mainD := by unfold mainD mainAlpha; positivity
  have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hOp0 : 0 ≤ mainOp (b ^ 2) := by unfold mainOp; positivity
  have hOm0 : 0 ≤ mainOm (b ^ 2) := by unfold mainOm; positivity
  -- deterministic profile averages
  have hOp : finAvg S (fun U => oldSignedFlatOscillationSize Q U b L true ^ 2) ≤
      mainOp (b ^ 2) ^ 2 := by
    exact main_oldSignedFlatPlus_descendant_average_le_mainOp_sq_scale Q d b hbpos L hrQ
  have hOm : finAvg S (fun U => oldSignedFlatOscillationSize Q U b L false ^ 2) ≤
      mainOm (b ^ 2) ^ 2 := by
    exact main_oldSignedFlatMinus_descendant_average_le_mainOm_sq_scale Q d b hbpos L hrQ
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
  have hxnn : 0 ≤ b ^ 2 + b ^ 2 * q / 2 := le_trans (sq_nonneg _) hl2p
  have hmeanP : finAvg S (fun U => oldSignedFlatMeanSize Q U b L true ^ 2) ≤
      Real.sqrt (b ^ 2 + b ^ 2 * q / 2) ^ 2 := by
    rw [Real.sq_sqrt hxnn]
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
  have hl2avg : finAvg S (fun U => oldSignedFlatL2Size Q U b L false ^ 2) ≤ |b| ^ 2 :=
    hpartM ▸ hl2m
  have hprof := L_profile_abstract S
    (fun U => oldSignedFlatOscillationSize Q U b L true)
    (fun U => oldSignedFlatOscillationSize Q U b L false)
    (fun U => oldSignedFlatL2Size Q U b L false)
    (fun U => oldSignedFlatMeanSize Q U b L true)
    (fun U => oldSignedFlatMeanSize Q U b L false)
    (fun U => Real.sqrt_nonneg _) (fun U => Real.sqrt_nonneg _) (fun U => Real.sqrt_nonneg _)
    (fun U => Real.sqrt_nonneg _) (fun U => Real.sqrt_nonneg _)
    (mainOp (b ^ 2)) (mainOm (b ^ 2)) |b| (Real.sqrt (b ^ 2 + b ^ 2 * q / 2))
    hOp0 hOm0 (abs_nonneg b) (Real.sqrt_nonneg _) hOp hOm hl2avg hmeanP hmeanM
    (2 * Real.sqrt (xi / 2)) mainBeta (2 * Real.sqrt (2 * (mainD * mainM0 H * H)))
    (mainM0 H) (2 * Real.sqrt 2 * mainKd (b ^ 2)) (Real.sqrt (xi / 2)) (mainBm H + 1)
    (by positivity) hβ (by positivity) hM0nn
    (mul_nonneg (by positivity) (mainKd_nonneg _)) (Real.sqrt_nonneg _)
    (by unfold mainBm; positivity)
  refine le_trans (le_of_eq ?_) (hprof.trans (le_of_eq ?_))
  · rfl
  · have hA : 2 * Real.sqrt (xi / 2) = Real.sqrt 2 * Real.sqrt xi := by
      rw [← Real.sqrt_mul (by norm_num)]
      rw [show (2 : ℝ) * xi = 2 ^ 2 * (xi / 2) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    have hD : Real.sqrt 2 * Real.sqrt (xi / 2) = Real.sqrt xi := by
      rw [← Real.sqrt_mul (by norm_num)]
      congr 1
      ring
    have hB : Real.sqrt (2 * (mainD * mainM0 H * H)) =
        Real.sqrt 2 * Real.sqrt (mainD * mainM0 H * H) := Real.sqrt_mul (by norm_num) _
    unfold mainLinearError mainT0 mainTm mainC
    rw [Real.sqrt_sq_eq_abs, hB]
    linear_combination
      (Real.sqrt (b ^ 2 + b ^ 2 * q / 2) * mainOp (b ^ 2)) * hA +
        (2 * mainKd (b ^ 2) * |b|) * hD

end
end ASDExplicitGamma.Main
end
