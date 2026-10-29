module

public import ASDExplicitGamma.Main.HotTrialExpectationsSplit
public import ASDExplicitGamma.Main.EnvelopeXIActual
public import ASDExplicitGamma.Main.EnvelopeHTransport
public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment

/-! Package D, generic positive split: for any nonnegative `L²` drop `Δ` with `‖Δ‖₂ ≤ H_d` and mean `c`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped ENNReal

noncomputable section

/-- Generic positive split. -/
theorem main_hot_positive_split_generic
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (Δ : Cutoff.CutoffSample 2 → ℝ) (c : ℝ)
    (hΔ0 : ∀ ω, 0 ≤ Δ ω)
    (hΔmem : MemLp Δ 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hΔnorm : lpNorm Δ 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      mainEnvelopeH (theta M) M.gamma t / (1 - mainAlpha))
    (hΔint : Integrable Δ (Cutoff.cutoffSampleLaw M).toMeasure)
    (hΔeq : (∫ ω, Δ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) = c) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let B : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
    let Hd := mainEnvelopeH (theta M) M.gamma t / (1 - mainAlpha)
    Integrable (fun ω => B ω * Δ ω) μ ∧
    (∫ ω, B ω * Δ ω ∂μ) ≤
      mainBeta * c +
        mainEpsNew * Hd ∧
    Integrable (fun ω => B ω ^ 2 * Δ ω) μ ∧
    (∫ ω, B ω ^ 2 * Δ ω ∂μ) ≤
      mainBeta ^ 2 * c +
        (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) * Hd := by
  classical
  intro μ B Hd
  let β : ℝ := 14103 / 10000
  let ε : ℝ := 1 / 10 ^ 24
  let Rg : Cutoff.CutoffSample 2 → ℝ := inverseBankPopulationRemainder
    .globalInverse (mixedBridgeObserverSourceRoots m) M m (m + 40)
    (bankPartialInsertionWeights m 1 t)
  have hpastM : ∀ n ≤ m, nativeInductionState M h n :=
    fun n hn => hpast n (lt_of_le_of_lt hn hm)
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) :=
    fun j => hpast _ (by omega)
  have hglobal := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have hglobalBank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hβ0 : 0 ≤ β := by norm_num [β]
  have hε0 : 0 ≤ ε := by norm_num [ε]
  have hB0 (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω :=
    mixed_bridge_bstar_nonneg M m t ω
  have hB128ENN : eLpNorm (fun ω => ENNReal.ofReal (B ω)) 128 μ ≤
      ENNReal.ofReal β := by
    simpa [B, β, inverseBankCap, μ] using hglobal.2.1
  have hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β := by
    rw [← eLpNorm_ofReal B (Filter.Eventually.of_forall hB0)]
    exact hB128ENN
  have hBmeas : AEStronglyMeasurable B μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top
      (hB128.trans_lt ENNReal.ofReal_lt_top).ne
  have hR0 (ω : Cutoff.CutoffSample 2) : 0 ≤ Rg ω := by
    simpa [Rg] using hglobalBank.remainder_nonneg ω
  have hRmeas : AEStronglyMeasurable Rg μ := by
    simpa [Rg, μ] using hglobalBank.remainder_measurable.aestronglyMeasurable
  have hR128 : eLpNorm Rg 128 μ ≤ ENNReal.ofReal ε := by
    simpa [Rg, μ, ε, inverseBankReserve] using hglobal.2.2
  have hBsplit : ∀ᵐ ω ∂μ, B ω ≤ β + Rg ω := by
    filter_upwards [hglobal.1] with ω hω
    have hω' : ENNReal.ofReal (B ω) ≤
        ENNReal.ofReal β + ENNReal.ofReal (Rg ω) := by
      simpa [B, β, Rg, inverseBankCap] using hω
    rw [← ENNReal.ofReal_add hβ0 (hR0 ω)] at hω'
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hβ0 (hR0 ω))).mp hω'
  have hHd0 : 0 ≤ Hd := (lpNorm_nonneg).trans hΔnorm
  have hΔ2 : eLpNorm Δ 2 μ ≤ ENNReal.ofReal Hd := by
    have : eLpNorm Δ 2 μ = ENNReal.ofReal (lpNorm Δ 2 μ) := by
      rw [lpNorm, ENNReal.ofReal_toReal hΔmem.eLpNorm_ne_top]
    rw [this]
    exact ENNReal.ofReal_le_ofReal hΔnorm
  have hΔmeas : AEStronglyMeasurable Δ μ := hΔmem.aestronglyMeasurable
  have hgen (k : ℕ) (hk : k ≤ 3) :
      Integrable (fun ω => B ω ^ k * Δ ω) μ ∧
      (∫ ω, B ω ^ k * Δ ω ∂μ) ≤
        β ^ k * (∫ ω, Δ ω ∂μ) + rareExpansionTail β ε Hd k := by
    have htail := old_signed_rare_power_tail_payment Rg Δ β ε Hd k (by omega)
      hβ0 hε0 hHd0 hR0 hΔ0 hRmeas hΔmeas hR128 hΔ2
    have hrhsInt : Integrable
        (fun ω => β ^ k * Δ ω + rareExpansionTail β (Rg ω) (Δ ω) k) μ :=
      (hΔint.const_mul (β ^ k)).add htail.1
    have hpt : ∀ᵐ ω ∂μ, B ω ^ k * Δ ω ≤
        β ^ k * Δ ω + rareExpansionTail β (Rg ω) (Δ ω) k := by
      filter_upwards [hBsplit] with ω hω
      have hpow : B ω ^ k ≤ (β + Rg ω) ^ k := pow_le_pow_left₀ (hB0 ω) hω k
      calc
        B ω ^ k * Δ ω ≤ (β + Rg ω) ^ k * Δ ω :=
          mul_le_mul_of_nonneg_right hpow (hΔ0 ω)
        _ = _ := rare_expansion_binomial β (Rg ω) (Δ ω) k hk
    refine ⟨?_, ?_⟩
    · refine hrhsInt.mono' ((hBmeas.pow k).mul hΔmeas) ?_
      filter_upwards [hpt] with ω hω
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hB0 ω) k) (hΔ0 ω))]
      exact hω
    · have hint : Integrable (fun ω => B ω ^ k * Δ ω) μ := by
        refine hrhsInt.mono' ((hBmeas.pow k).mul hΔmeas) ?_
        filter_upwards [hpt] with ω hω
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hB0 ω) k) (hΔ0 ω))]
        exact hω
      calc
        (∫ ω, B ω ^ k * Δ ω ∂μ) ≤
            ∫ ω, (β ^ k * Δ ω + rareExpansionTail β (Rg ω) (Δ ω) k) ∂μ :=
          integral_mono_ae hint hrhsInt hpt
        _ = β ^ k * (∫ ω, Δ ω ∂μ) +
            ∫ ω, rareExpansionTail β (Rg ω) (Δ ω) k ∂μ := by
          rw [integral_add (hΔint.const_mul (β ^ k)) htail.1, integral_const_mul]
        _ ≤ _ := add_le_add_right htail.2 _
  have h1 := hgen 1 (by norm_num)
  have h2 := hgen 2 (by norm_num)
  have ht1 : rareExpansionTail β ε Hd 1 = ε * Hd := by
    simp [rareExpansionTail]
  have ht2 : rareExpansionTail β ε Hd 2 = (2 * β * ε + ε ^ 2) * Hd := by
    norm_num [rareExpansionTail, Finset.sum_Icc_succ_top]
    ring
  have hβm : mainBeta = β := rfl
  have hεm : mainEpsNew = ε := rfl
  rw [hΔeq] at h1 h2
  refine ⟨by simpa using h1.1, ?_, h2.1, ?_⟩
  · rw [hβm, hεm]
    have := h1.2
    rw [ht1] at this
    simpa using this
  · rw [hβm, hεm]
    have := h2.2
    rw [ht2] at this
    exact this

end

end ASDExplicitGamma.Main
