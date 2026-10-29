module

public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Inverse.BridgeTraceSummability
public import ASDExplicitGamma.Native.OldSignedDepthSeriesArithmetic
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.OldSignedQuarterRareReserve
public import ASDExplicitGamma.Native.OldSignedRarePowerPayment
public import ASDExplicitGamma.Native.OldSignedRareTailProduct
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The global-population rare payment in the actual OLD parent-gap series. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Scalar
open scoped ENNReal

noncomputable section

private theorem parent_gap_global_rare_tail_thirteen
    (ε C : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000)
    (hC : 0 ≤ C) (k : ℕ) (hk : k ≤ 3) :
    rareExpansionTail (14103 / 10000 : ℝ) ε C k ≤ 13 * ε * C := by
  have hε2 : ε ^ 2 ≤ ε * (1 / 1000 : ℝ) := by
    have hdiff : 0 ≤ (1 / 1000 : ℝ) - ε := sub_nonneg.mpr hεsmall
    nlinarith [mul_nonneg hε hdiff]
  have hε3 : ε ^ 3 ≤ ε * (1 / 1000 : ℝ) ^ 2 := by
    calc
      ε ^ 3 = ε ^ 2 * ε := by ring
      _ ≤ (ε * (1 / 1000 : ℝ)) * ε :=
        mul_le_mul_of_nonneg_right hε2 hε
      _ = ε ^ 2 * (1 / 1000 : ℝ) := by ring
      _ ≤ (ε * (1 / 1000 : ℝ)) * (1 / 1000 : ℝ) :=
        mul_le_mul_of_nonneg_right hε2 (by norm_num)
      _ = ε * (1 / 1000 : ℝ) ^ 2 := by ring
  have hscalar :
      rareExpansionTail (14103 / 10000 : ℝ) ε 1 k ≤ 13 * ε := by
    interval_cases k <;>
      norm_num [rareExpansionTail, Finset.sum_Icc_succ_top, Nat.choose] <;>
      nlinarith [hε, hε2, hε3]
  rw [old_signed_rare_tail_linear (14103 / 10000 : ℝ) ε C k]
  exact mul_le_mul_of_nonneg_right hscalar hC

private theorem parent_gap_nonnegative_series_integral_ae
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (f : I → Ω → ℝ) (C : I → ℝ)
    (hf : ∀ j, Integrable (f j) μ)
    (hn : ∀ j ω, 0 ≤ f j ω)
    (hs : ∀ᵐ ω ∂μ, Summable (fun j => f j ω))
    (hC : Summable C)
    (hb : ∀ j, (∫ ω, f j ω ∂μ) ≤ C j) :
    Integrable (fun ω => ∑' j, f j ω) μ ∧
      (∫ ω, ∑' j, f j ω ∂μ) ≤ ∑' j, C j := by
  classical
  have hI : Summable (fun j => ∫ ω, f j ω ∂μ) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg (hn j)) hb hC
  have hm : AEStronglyMeasurable (fun ω => ∑' j, f j ω) μ := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun s : Finset I => s.aestronglyMeasurable_fun_sum
        (fun j _ => (hf j).1))
    filter_upwards [hs] with ω hω
    exact hω.hasSum
  have hsumENN : ∀ᵐ ω ∂μ,
      ENNReal.ofReal (∑' j, f j ω) = ∑' j, ENNReal.ofReal (f j ω) := by
    filter_upwards [hs] with ω hω
    exact ENNReal.ofReal_tsum_of_nonneg (fun j => hn j ω) hω
  have he :
      (∫⁻ ω, ENNReal.ofReal (∑' j, f j ω) ∂μ) =
        ENNReal.ofReal (∑' j, ∫ ω, f j ω ∂μ) := by
    rw [lintegral_congr_ae hsumENN,
      lintegral_tsum
        (fun j => (hf j).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hf _)
      (Filter.Eventually.of_forall (hn _))]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun j => integral_nonneg (hn j)) hI).symm
  have hi : Integrable (fun ω => ∑' j, f j ω) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hm
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun j => hn j ω)))).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  have hnorm : Summable (fun j => ∫ ω, ‖f j ω‖ ∂μ) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using hI
  refine ⟨hi, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hf hnorm]
  exact hI.tsum_le_tsum hb hC

/-- The complete global-population rare remainder at each OLD weak depth is
integrable and pays its source reserve. This is the component used in
the centered-baseline and final parent-gap assembly. -/
theorem parent_gap_global_population_rare_series
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : k ≤ 3) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let R := inverseBankPopulationRemainder .globalInverse
      (mixedBridgeObserverSourceRoots m) M m (m + 40)
      (bankPartialInsertionWeights m 1 t)
    Integrable (fun ω => ∑' j : ℕ,
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        rareExpansionTail (14103 / 10000 : ℝ) (R ω)
          (mixedBridgeOldInverseBaseline M j *
            mixedBridgeTbar M m t ω j) k) μ ∧
    (∫ ω, ∑' j : ℕ,
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        rareExpansionTail (14103 / 10000 : ℝ) (R ω)
          (mixedBridgeOldInverseBaseline M j *
            mixedBridgeTbar M m t ω j) k ∂μ) ≤
      ((14103 / 10000 : ℝ) ^ k) * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let R : Cutoff.CutoffSample 2 → ℝ :=
    inverseBankPopulationRemainder .globalInverse
      (mixedBridgeObserverSourceRoots m) M m (m + 40)
      (bankPartialInsertionWeights m 1 t)
  let α : ℝ := Scalar.inverseHistoryDiscount
  let ε : ℝ := 1 / 10 ^ 24
  let β : ℝ := 14103 / 10000
  let b₀ : ℝ := 3683 / 2500
  let Q : TriadicCube 2 := originCube 2 m
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    mixedBridgeTbar M m t ω j
  let C : ℕ → ℝ := fun j =>
    theta M * (invTraceM : ℝ) * (1 + (j : ℝ)) ^ 2 *
      (3 : ℝ) ^ (6 * gammaZero * j)
  let b : ℕ → ℝ := fun j => mixedBridgeOldInverseBaseline M j
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let f : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    w j * b j * rareExpansionTail β (R ω) (T j ω) k
  let budget : ℕ → ℝ := fun j => w j * b j * (13 * ε * C j)

  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    apply hpast
    omega
  have hstate0 : ∀ j : ℕ,
      nativeInductionState M h (m - (0 : ℤ) - (j : ℤ)) := by
    intro j
    simpa using hstate j

  have hbank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hsplit := mixed_bridge_global_bank_split M h hM hγ m t ht hstate
  have _hBstarSplit := hsplit.1
  have _hBstarCap := hsplit.2.1
  have hRnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ R ω := by
    exact hbank.remainder_nonneg ω
  have hRmeas : AEStronglyMeasurable R μ := by
    simpa [R, μ] using hbank.remainder_measurable.aestronglyMeasurable
  have hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε := by
    simpa [R, μ, ε, inverseBankReserve] using hsplit.2.2

  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hinvTrace : 0 ≤ invTraceM := by
    rw [invTrace_coefficient.1]
    positivity
  have hinvTraceReal : 0 ≤ (invTraceM : ℝ) := by
    exact_mod_cast hinvTrace
  have hαrange := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := by dsimp [α]; exact hαrange.1.le
  have hα1 : α ≤ 1 := by dsimp [α]; exact hαrange.2.le
  have hw0 (j : ℕ) : 0 ≤ w j := by
    dsimp [w]
    have hsq : α ^ 2 ≤ 1 := by nlinarith [hα1]
    exact mul_nonneg (sub_nonneg.mpr hsq) (pow_nonneg hα0 _)
  have hweight0 : 0 ≤ 1 - α ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ hα0 hα1)
  have hb0 : 0 ≤ b₀ := by norm_num [b₀]
  have hb0le : 1 ≤ b₀ := by norm_num [b₀]
  have hβ0 : 0 ≤ β := by norm_num [β]
  have hβ1 : 1 ≤ β := by norm_num [β]
  have hε0 : 0 ≤ ε := by norm_num [ε]
  have hεsmall : ε ≤ 1 / 1000 := by norm_num [ε]
  have hC0 (j : ℕ) : 0 ≤ C j := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (mul_nonneg htheta hinvTraceReal)
      (sq_nonneg _)) (Real.rpow_nonneg (by norm_num) _)
  have hb0j (j : ℕ) : 0 ≤ b j := by
    dsimp [b, mixedBridgeOldInverseBaseline]
    exact mul_nonneg hb0 (Real.rpow_nonneg (by norm_num) _)
  have hTnonneg (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    simpa [T, Q, mixedBridgeTbar] using
      raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j

  let hShell := raw_trace_transport_shell_family_source
    M h hM hγ m 0 t ht hstate0
  let hMem := rawWeakTraceSequenceMemLpFromShellTransport
    M h hγ m 0 (by omega) t ht hstate0 hShell
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m 0 (by omega) t ht hstate0 hShell
  have hTmem (j : ℕ) : MemLp (T j) 2 μ := by
    simpa [T, Q, μ, mixedBridgeTbar] using hMem j
  have hTprofile (j : ℕ) : eLpNorm (T j) 2 μ ≤ ENNReal.ofReal (C j) := by
    simpa [T, Q, μ, C, mixedBridgeTbar,
      rawWeakTraceProfileEnvelope] using hprofile j
  have hTmeas (j : ℕ) : AEStronglyMeasurable (T j) μ :=
    (hTmem j).aestronglyMeasurable

  have htail (j : ℕ) :
      Integrable (fun ω => rareExpansionTail β (R ω) (T j ω) k) μ ∧
      (∫ ω, rareExpansionTail β (R ω) (T j ω) k ∂μ) ≤
        rareExpansionTail β ε (C j) k := by
    exact old_signed_rare_power_tail_payment R (T j) β ε (C j) k (by omega)
      hβ0 hε0 (hC0 j) hRnonneg (hTnonneg j)
      hRmeas (hTmeas j) hR128 (hTprofile j)

  have htailLinear (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      rareExpansionTail β (R ω) (b j * T j ω) k =
        b j * rareExpansionTail β (R ω) (T j ω) k := by
    rw [old_signed_rare_tail_linear β (R ω) (b j * T j ω) k,
      old_signed_rare_tail_linear β (R ω) (T j ω) k]
    ring
  have hfIntegrable (j : ℕ) : Integrable (f j) μ := by
    have hEq : f j = fun ω => (w j * b j) *
        rareExpansionTail β (R ω) (T j ω) k := by
      funext ω
      dsimp [f]
    rw [hEq]
    exact (htail j).1.const_mul (w j * b j)

  have hbudgetNonneg (j : ℕ) : 0 ≤ budget j := by
    dsimp [budget]
    exact mul_nonneg (mul_nonneg (hw0 j) (hb0j j))
      (mul_nonneg (mul_nonneg (by norm_num) (hε0)) (hC0 j))
  have hbudgetPay (j : ℕ) : (∫ ω, f j ω ∂μ) ≤ budget j := by
    have hEq : f j = fun ω => (w j * b j) *
        rareExpansionTail β (R ω) (T j ω) k := by
      funext ω
      dsimp [f]
    rw [hEq, integral_const_mul]
    have htailNum := parent_gap_global_rare_tail_thirteen ε (C j)
      hε0 hεsmall (hC0 j) k hk
    calc
      _ ≤ (w j * b j) * rareExpansionTail β ε (C j) k :=
        mul_le_mul_of_nonneg_left (htail j).2
          (mul_nonneg (hw0 j) (hb0j j))
      _ ≤ (w j * b j) * (13 * ε * C j) :=
        mul_le_mul_of_nonneg_left htailNum
          (mul_nonneg (hw0 j) (hb0j j))
      _ = budget j := by rfl

  have hrawSum := mixed_bridge_raw_trace_weighted_summable_ae
    M h hM hγ m t ht hstate
  have hαrpow : α = (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    dsimp [α]
    rw [inverse_history_discount_eq,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have hfactorBound : α * (3 : ℝ) ^ (2 * M.gamma) ≤ 1 := by
    have hg0 : 0 ≤ gammaZero := by norm_num [gammaZero]
    have hexp : -(1 / 4 : ℝ) + 2 * M.gamma ≤
        -(1 / 4 : ℝ) + 6 * gammaZero := by nlinarith [hγ, hg0]
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 3) hexp
    calc
      _ = (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
        rw [hαrpow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ ≤ (3 : ℝ) ^ (-(1 / 4 : ℝ) + 6 * gammaZero) := hpow
      _ ≤ 1 := by
        exact old_signed_quarter_trace_ratio.trans (by norm_num)
  have hfactor0 : 0 ≤ α * (3 : ℝ) ^ (2 * M.gamma) := by positivity
  have hfactorPow (j : ℕ) :
      α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
        (α * (3 : ℝ) ^ (2 * M.gamma)) ^ j := by
    have h3pow (j : ℕ) :
        (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
          ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
      rw [show 2 * M.gamma * (j : ℝ) =
        (2 * M.gamma) * (j : ℝ) by ring]
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j]
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [h3pow, ← mul_pow]
  have hfactorPowLe (j : ℕ) :
      α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ 1 := by
    rw [hfactorPow]
    exact pow_le_one₀ hfactor0 hfactorBound

  have htailConstNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ rareExpansionTail β (R ω) 1 k := by
    unfold rareExpansionTail
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ0 _))
      (pow_nonneg (hRnonneg ω) _)) (by norm_num)
  have hshape (j : ℕ) (ω : Cutoff.CutoffSample 2) :
      f j ω =
        ((1 - α ^ 2) * b₀ * rareExpansionTail β (R ω) 1 k) *
          ((α ^ j * T j ω) *
            (α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)))) := by
    dsimp [f, w, b, mixedBridgeOldInverseBaseline]
    rw [old_signed_rare_tail_linear β (R ω) (T j ω) k]
    have hpow : α ^ (2 * j) = α ^ j * α ^ j := by
      rw [show 2 * j = j + j by omega, pow_add]
    rw [hpow]
    ring
  have hsumPointwise : ∀ᵐ ω ∂μ, Summable (fun j : ℕ => f j ω) := by
    filter_upwards [hrawSum] with ω hω
    have hω' : Summable (fun j : ℕ => α ^ j * T j ω) := by
      simpa [T] using hω
    let cω := (1 - α ^ 2) * b₀ * rareExpansionTail β (R ω) 1 k
    have hcω : 0 ≤ cω := by
      dsimp [cω]
      exact mul_nonneg (mul_nonneg hweight0 hb0)
        (htailConstNonneg ω)
    have hterm0 (j : ℕ) : 0 ≤ α ^ j * T j ω :=
      mul_nonneg (pow_nonneg hα0 _) (hTnonneg j ω)
    have hfactorNonneg (j : ℕ) :
        0 ≤ α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
      rw [hfactorPow j]
      exact pow_nonneg hfactor0 j
    have hdom (j : ℕ) : f j ω ≤ cω * (α ^ j * T j ω) := by
      rw [hshape j ω]
      calc
        _ ≤ cω * ((α ^ j * T j ω) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hfactorPowLe j) (hterm0 j)) hcω
        _ = _ := by simp
    exact Summable.of_nonneg_of_le (fun j => by
      rw [hshape j ω]
      exact mul_nonneg hcω (mul_nonneg (hterm0 j)
        (hfactorNonneg j))) hdom (hω'.mul_left cω)

  let q : ℝ := (3 : ℝ) ^ (-(1 / 2 : ℝ) + 2 * M.gamma +
    6 * gammaZero + 1 / 64)
  let c : ℝ := (1 - α ^ 2) * b₀ * (13 * ε) * theta M * (invTraceM : ℝ)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg (by norm_num) _
  have hqratio : q ≤ 9 / 10 := by
    dsimp [q]
    exact old_signed_depth_rare_ratio M hγ
  have hgeom := native_source_quadratic_geometric_sum (9 / 10 : ℝ)
    (by norm_num) (by norm_num)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hweight0 hb0)
      (mul_nonneg (by norm_num) hε0)) htheta) hinvTraceReal
  have hpop (j : ℕ) : 1 ≤ (9 : ℝ) ^ ((j : ℝ) / 128) := by
    apply Real.one_le_rpow (by norm_num)
    positivity
  have hdepthExp (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
        (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) ≤ q ^ j := by
    have hA0 : 0 ≤ α ^ (2 * j) * bankDepthFrame M j :=
      mul_nonneg (pow_nonneg hα0 _) (bankDepthFrame_pos M j).le
    have hP0 : 0 ≤ (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      _ = (α ^ (2 * j) * bankDepthFrame M j) * 1 *
          (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) := by
        simp [bankDepthFrame]
      _ ≤ (α ^ (2 * j) * bankDepthFrame M j) *
          (9 : ℝ) ^ ((j : ℝ) / 128) *
          (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left (hpop j) hA0
        exact mul_le_mul_of_nonneg_right hmul hP0
      _ = q ^ j := by
        simpa [q] using old_signed_depth_rare_weight M j
  have hdepthExp09 (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
        (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)) ≤ (9 / 10 : ℝ) ^ j := by
    exact (hdepthExp j).trans (pow_le_pow_left₀ hq0 hqratio j)

  have hbudgetNN (j : ℕ) : 0 ≤ budget j := hbudgetNonneg j
  have hbudgetShape (j : ℕ) :
      budget j = c * (((j : ℝ) + 1) ^ 2 *
        (α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) *
          (3 : ℝ) ^ (6 * gammaZero * (j : ℝ)))) := by
    dsimp [budget, w, b, C, c, mixedBridgeOldInverseBaseline]
    ring
  have hbudgetBound (j : ℕ) :
      budget j ≤ c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j) := by
    rw [hbudgetShape j]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hdepthExp09 j) (sq_nonneg _)) hc0
  have hbudgetDom : Summable (fun j : ℕ =>
      c * (((j : ℝ) + 1) ^ 2 * (9 / 10 : ℝ) ^ j)) := hgeom.1.mul_left c
  have hbudgetSummable : Summable budget :=
    Summable.of_nonneg_of_le hbudgetNN hbudgetBound hbudgetDom
  have hbudgetTsum : (∑' j : ℕ, budget j) ≤ c * 1900 := by
    have hsum := hbudgetSummable.tsum_le_tsum hbudgetBound hbudgetDom
    rw [tsum_mul_left, hgeom.2] at hsum
    norm_num only [show (1 + (9 / 10 : ℝ)) / (1 - 9 / 10) ^ 3 = 1900 by norm_num]
      at hsum
    exact hsum

  have htraceInvCap : (invTraceM : ℝ) ≤ 10 ^ 6 := by
    exact_mod_cast invTrace_coefficient.2.1.le
  have hconst : (1 - α ^ 2) * b₀ * (13 * ε) * 1900 * 10 ^ 6 ≤
      1 / (13 * 10 ^ 12 : ℝ) := by
    have hnum : b₀ * (13 * ε) * 1900 * 10 ^ 6 ≤
        1 / (13 * 10 ^ 12 : ℝ) := by norm_num [b₀, ε]
    have hcore0 : 0 ≤ b₀ * (13 * ε) * 1900 * 10 ^ 6 := by positivity
    have hfactorLe : 1 - α ^ 2 ≤ 1 := sub_le_self _ (sq_nonneg α)
    calc
      _ = (1 - α ^ 2) * (b₀ * (13 * ε) * 1900 * 10 ^ 6) := by ring
      _ ≤ 1 * (b₀ * (13 * ε) * 1900 * 10 ^ 6) :=
        mul_le_mul_of_nonneg_right hfactorLe hcore0
      _ = _ := by ring
      _ ≤ _ := hnum
  have hcoeffCap : c * 1900 ≤ theta M * (1 / (13 * 10 ^ 12 : ℝ)) := by
    have hcoeff0 : 0 ≤ (1 - α ^ 2) * b₀ * (13 * ε) * 1900 := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hweight0 hb0)
          (mul_nonneg (show 0 ≤ (13 : ℝ) by norm_num) hε0))
        (show 0 ≤ (1900 : ℝ) by norm_num)
    calc
      c * 1900 = theta M *
          ((1 - α ^ 2) * b₀ * (13 * ε) * 1900 * (invTraceM : ℝ)) := by
        dsimp [c]
        ring
      _ ≤ theta M *
          ((1 - α ^ 2) * b₀ * (13 * ε) * 1900 * 10 ^ 6) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left htraceInvCap hcoeff0) htheta
      _ ≤ theta M * (1 / (13 * 10 ^ 12 : ℝ)) :=
        mul_le_mul_of_nonneg_left hconst htheta
  have hβpow : 1 ≤ β ^ k := one_le_pow₀ hβ1
  have hreserve : 0 ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M :=
    mul_nonneg (by norm_num) htheta
  have hcoeffCap' : c * 1900 ≤
      (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ theta M * (1 / (13 * 10 ^ 12 : ℝ)) := hcoeffCap
      _ = _ := mul_comm _ _
  have hbudgetCap : c * 1900 ≤
      β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by
    calc
      _ ≤ (1 / (13 * 10 ^ 12 : ℝ)) * theta M := hcoeffCap'
      _ = 1 * ((1 / (13 * 10 ^ 12 : ℝ)) * theta M) := by ring
      _ ≤ β ^ k * ((1 / (13 * 10 ^ 12 : ℝ)) * theta M) :=
        mul_le_mul_of_nonneg_right hβpow hreserve
      _ = β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M := by ring

  have hseries := parent_gap_nonnegative_series_integral_ae μ f budget
    hfIntegrable (fun j ω =>
      mul_nonneg (mul_nonneg (hw0 j) (hb0j j))
        (by
          unfold rareExpansionTail
          apply Finset.sum_nonneg
          intro i hi
          exact mul_nonneg (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ0 _))
            (pow_nonneg (hRnonneg ω) _)) (hTnonneg j ω)))
    hsumPointwise hbudgetSummable hbudgetPay
  have htargetEq :
      (fun ω => ∑' j : ℕ, w j *
        rareExpansionTail β (R ω) (b j * T j ω) k) =
      (fun ω => ∑' j : ℕ, f j ω) := by
    funext ω
    apply tsum_congr
    intro j
    dsimp [f]
    rw [htailLinear j ω]
    ring
  change
    Integrable (fun ω => ∑' j : ℕ,
      w j * rareExpansionTail β (R ω) (b j * T j ω) k) μ ∧
    (∫ ω, ∑' j : ℕ,
      w j * rareExpansionTail β (R ω) (b j * T j ω) k ∂μ) ≤
      β ^ k * (1 / (13 * 10 ^ 12 : ℝ)) * theta M
  refine ⟨?_, ?_⟩
  · rw [htargetEq]
    exact hseries.1
  · rw [htargetEq]
    exact hseries.2.trans (hbudgetTsum.trans hbudgetCap)

/-- The actual global-population rare terms are summable almost everywhere.
The proof compares their pointwise series to the already-proved weighted raw
trace series; it does not infer pointwise convergence from integrability of a
real-valued tsum. -/
private theorem parent_gap_global_population_rare_series_pointwise_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (_hk : k ≤ 3) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let R := inverseBankPopulationRemainder .globalInverse
      (mixedBridgeObserverSourceRoots m) M m (m + 40)
      (bankPartialInsertionWeights m 1 t)
    ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        rareExpansionTail (14103 / 10000 : ℝ) (R ω)
          (mixedBridgeOldInverseBaseline M j *
            mixedBridgeTbar M m t ω j) k) := by
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let β : ℝ := 14103 / 10000
  let R : Cutoff.CutoffSample 2 → ℝ := inverseBankPopulationRemainder .globalInverse
    (mixedBridgeObserverSourceRoots m) M m (m + 40)
    (bankPartialInsertionWeights m 1 t)
  let b : ℕ → ℝ := mixedBridgeOldInverseBaseline M
  let w : ℕ → ℝ := fun j => (1 - α ^ 2) * α ^ (2 * j)
  let T : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω =>
    mixedBridgeTbar M m t ω j
  let X : ℕ → Cutoff.CutoffSample 2 → ℝ := fun j ω => b j * T j ω
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hαsq : 0 ≤ 1 - α ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ hα0 hα.2.le)
  have hβ0 : 0 ≤ β := by norm_num [β]
  have hstate : ∀ j : ℕ, nativeInductionState M h (m - (j : ℤ)) := by
    intro j
    apply hpast
    omega
  have hbank := mixed_bridge_global_bank_inputs M h hM hγ m t ht hstate
  have hR0 (ω : Cutoff.CutoffSample 2) : 0 ≤ R ω := by
    simpa [R] using hbank.remainder_nonneg ω
  have hT0 (j : ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m (originCube 2 m) t
      ⟨ht.1, ht.2⟩ ω j
  have htraceSummable := mixed_bridge_raw_trace_weighted_summable_ae
    M h hM hγ m t ht hstate
  have hfactor (j : ℕ) :
      α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ 1 := by
    have hgamma : 2 * M.gamma - 1 / 4 ≤ 0 := by
      dsimp [gammaZero] at hγ ⊢
      linarith
    have hpowEq : α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
        (3 : ℝ) ^ ((2 * M.gamma - 1 / 4) * (j : ℝ)) := by
      rw [Scalar.inverse_history_discount_power j,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    rw [hpowEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1 : ℝ) ≤ 3)
      (mul_nonpos_of_nonpos_of_nonneg hgamma (Nat.cast_nonneg j))
  have hpointwise : ∀ᵐ ω ∂μ,
      Summable (fun j : ℕ => w j *
        rareExpansionTail β (R ω) (X j ω) k) := by
    filter_upwards [htraceSummable] with ω hω
    let D : ℝ := rareExpansionTail β (R ω) 1 k
    let K : ℝ := D * (1 - α ^ 2) * (3683 / 2500 : ℝ)
    have hD0 : 0 ≤ D := by
      dsimp [D, rareExpansionTail]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hβ0 _))
          (pow_nonneg (hR0 ω) _))
        (by norm_num)
    have hK0 : 0 ≤ K := by
      dsimp [K]
      exact mul_nonneg (mul_nonneg hD0 hαsq) (by norm_num)
    have hsum : Summable (fun j : ℕ => α ^ j * T j ω) := by
      simpa [T] using hω
    have hmajor (j : ℕ) :
        w j * rareExpansionTail β (R ω) (X j ω) k ≤
          K * (α ^ j * T j ω) := by
      have hlinear : rareExpansionTail β (R ω) (X j ω) k = D * X j ω := by
        dsimp [D, X]
        unfold rareExpansionTail
        simp only [mul_one, Finset.sum_mul]
      have heq : w j * rareExpansionTail β (R ω) (X j ω) k =
          K * (α ^ j * T j ω) *
            (α ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by
        rw [hlinear]
        dsimp [w, X, b, mixedBridgeOldInverseBaseline, K]
        rw [show 2 * j = j + j by omega, pow_add]
        ring
      rw [heq]
      calc
        _ ≤ K * (α ^ j * T j ω) * 1 :=
          mul_le_mul_of_nonneg_left (hfactor j)
            (mul_nonneg hK0 (mul_nonneg (pow_nonneg hα0 j) (hT0 j ω)))
        _ = _ := by ring
    have hnonneg (j : ℕ) :
        0 ≤ w j * rareExpansionTail β (R ω) (X j ω) k := by
      apply mul_nonneg (by
        dsimp [w]
        exact mul_nonneg hαsq (pow_nonneg hα0 _))
      have hlinear : rareExpansionTail β (R ω) (X j ω) k = D * X j ω := by
        dsimp [D, X]
        unfold rareExpansionTail
        simp only [mul_one, Finset.sum_mul]
      rw [hlinear]
      exact mul_nonneg hD0 (mul_nonneg
        (by dsimp [b, mixedBridgeOldInverseBaseline]; positivity)
        (hT0 j ω))
    have hsum' := Summable.of_nonneg_of_le hnonneg hmajor (hsum.mul_left K)
    simpa only [R, T, X, b, w, α, β, μ] using hsum'
  simpa only [R, T, b, w, α, β, μ] using hpointwise

/-- The global-population rare payment together with the almost-everywhere
pointwise summability needed by real-tsum comparisons in the parent assembly. -/
theorem parent_gap_global_population_rare_series_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (k : ℕ) (hk : k ≤ 3) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let R := inverseBankPopulationRemainder .globalInverse
      (mixedBridgeObserverSourceRoots m) M m (m + 40)
      (bankPartialInsertionWeights m 1 t)
    Integrable (fun ω => ∑' j : ℕ,
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        rareExpansionTail (14103 / 10000 : ℝ) (R ω)
          (mixedBridgeOldInverseBaseline M j *
            mixedBridgeTbar M m t ω j) k) μ ∧
    (∫ ω, ∑' j : ℕ,
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        rareExpansionTail (14103 / 10000 : ℝ) (R ω)
          (mixedBridgeOldInverseBaseline M j *
            mixedBridgeTbar M m t ω j) k ∂μ) ≤
      ((14103 / 10000 : ℝ) ^ k) * (1 / (13 * 10 ^ 12 : ℝ)) * theta M ∧
    ∀ᵐ ω ∂μ, Summable (fun j : ℕ =>
      ((1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j)) *
        rareExpansionTail (14103 / 10000 : ℝ) (R ω)
          (mixedBridgeOldInverseBaseline M j *
            mixedBridgeTbar M m t ω j) k) := by
  have hseries := parent_gap_global_population_rare_series
    M h hM hγ N hpast m hm t ht k hk
  have hpointwise := parent_gap_global_population_rare_series_pointwise_summable
    M h hM hγ N hpast m hm t ht k hk
  exact ⟨hseries.1, hseries.2, hpointwise⟩

end
end ASDExplicitGamma.Inverse
