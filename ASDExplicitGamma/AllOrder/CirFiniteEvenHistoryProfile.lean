/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenHistory
public import ASDExplicitGamma.AllOrder.CirFiniteEvenHistorySeries
public import ASDExplicitGamma.AllOrder.CirInverseHistoryProfile
public import ASDExplicitGamma.Inverse.HistoryLpSeries

/-! # Lp envelope for the reset inverse-history series -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Inverse
open Homogenization.Book
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

noncomputable section

/-- The root maxima at all depths above a starting descendant layer, with
the source's normalized geometric history discount. -/
def aoCirResetInverseDepthProfileSeries (M : ABKModel 2) (Q : TriadicCube 2)
    (j : ℕ) (N : ℤ) (q : ℝ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1 - aoCirInverseHistoryDiscount) *
    ∑' d : ℕ, aoCirInverseHistoryDiscount ^ d *
      aoCirResetInverseDepthMax M Q (j + d) N Q.scale q t ω

private theorem aoCir_reset_inverse_depth_max_nonneg
    (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (N K₀ : ℤ)
    (q : ℝ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ aoCirResetInverseDepthMax M Q d N K₀ q t ω := by
  unfold aoCirResetInverseDepthMax
  apply Book.Ch02.finsetSupReal_nonneg
  intro R hR
  unfold rootInverseObservable
  exact mul_nonneg (Annealed.sigmaBar_characterization M K₀).1.le (norm_nonneg _)

private theorem aoCir_descendant_population_factor (Q : TriadicCube 2)
    (j d : ℕ) (q : ℝ) :
    ((descendantsAtDepth Q (j + d)).card : ℝ≥0∞) ^ (1 / q : ℝ) =
      ENNReal.ofReal (Real.rpow 9 (((j + d : ℕ) : ℝ) / q)) := by
  have hcardR : ((descendantsAtDepth Q (j + d)).card : ℝ) =
      (9 : ℝ) ^ (j + d) := by
    simp only [descendantsAtDepth_card]
    norm_num
  have hcardPos : 0 < ((descendantsAtDepth Q (j + d)).card : ℝ) := by
    rw [hcardR]
    positivity
  have hroot :
      Real.rpow ((descendantsAtDepth Q (j + d)).card : ℝ) (1 / q) =
        Real.rpow 9 (((j + d : ℕ) : ℝ) / q) := by
    rw [hcardR]
    calc
      Real.rpow ((9 : ℝ) ^ (j + d)) (1 / q) =
          Real.rpow 9 ((j + d : ℕ) * (1 / q)) := by
        exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 9)
          (j + d) (1 / q)).symm
      _ = Real.rpow 9 (((j + d : ℕ) : ℝ) / q) := by
        congr 1
        push_cast
        ring
  have hcast : ((descendantsAtDepth Q (j + d)).card : ℝ≥0∞) =
      ENNReal.ofReal ((descendantsAtDepth Q (j + d)).card : ℝ) := by norm_cast
  calc
    _ = ENNReal.ofReal ((descendantsAtDepth Q (j + d)).card : ℝ) ^ (1 / q) := by
      rw [hcast]
    _ = ENNReal.ofReal
        (Real.rpow ((descendantsAtDepth Q (j + d)).card : ℝ) (1 / q)) :=
      ENNReal.ofReal_rpow_of_pos hcardPos
    _ = _ := by rw [hroot]

private theorem aoCir_reset_inverse_depth_max_measurable
    (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (N K₀ : ℤ)
    (q t : ℝ) :
    Measurable (aoCirResetInverseDepthMax M Q d N K₀ q t) := by
  classical
  let S := descendantsAtDepth Q d
  have hS : S.Nonempty := descendantsAtDepth_nonempty Q d
  have hroot : ∀ R : TriadicCube 2, Measurable (fun ω =>
      rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N K₀
        (aoCirStepWeights N t) ω) := by
    intro R
    have hratio := root_inverse_observable_eq_reference_ratio M R
      (protectedOldLabel R.scale (orderBand q)) N K₀
      (aoCirStepWeights N t)
    have heq : (fun ω => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N K₀
        (aoCirStepWeights N t) ω) =
      (fun ω => ((Annealed.sigmaBar M K₀ : ℝ) /
        (Annealed.sigmaBar M
          (protectedOldLabel R.scale (orderBand q)) : ℝ)) *
        rootInverseResponse M R
          (protectedOldLabel R.scale (orderBand q)) N
          (aoCirStepWeights N t) ω) := funext hratio
    rw [heq]
    exact measurable_const.mul (root_inverse_response_measurable M
      (protectedOldLabel R.scale (orderBand q)) N
      (aoCirStepWeights N t) R)
  have hsup : Measurable (S.sup' hS fun R ω =>
      rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N K₀
        (aoCirStepWeights N t) ω) :=
    Finset.measurable_sup' hS (fun R _ => hroot R)
  have heq : aoCirResetInverseDepthMax M Q d N K₀ q t =
      S.sup' hS (fun R ω =>
        rootInverseObservable M R
          (protectedOldLabel R.scale (orderBand q)) N K₀
          (aoCirStepWeights N t) ω) := by
    funext ω
    change Book.Ch02.finsetSupReal S _ = _
    rw [Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS]
    simp only [Finset.sup'_apply]
  rw [heq]
  exact hsup

/-- The reset-derived Lp bound for the complete inverse-history profile
series, including the depth population cost. -/
theorem aoCir_reset_inverse_depth_profile_series_bound
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ n : ℤ, nativeInductionState M h n)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale ≤ N)
    (j : ℕ) (q : ℝ) (hq48 : 48 ≤ q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (aoCirResetInverseDepthProfileSeries M Q j N q t)
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aoCirInverseHistoryFactor M.gamma *
        Real.rpow 9 ((j : ℝ) / q) *
        orderInverseProfile (153 / 100) M.gamma q ((j : ℝ) + 1)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let r := aoCirInverseHistoryDiscount
  let profileTerm (d : ℕ) := Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
    orderInverseProfile (153 / 100) M.gamma q (((j + d : ℕ) : ℝ) + 1)
  have hqpos : 0 < q := by linarith
  have hqENN : 1 ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ q)
  have hr0 : 0 ≤ r := by dsimp [r, aoCirInverseHistoryDiscount]; positivity
  have hr1 : r < 1 := by
    dsimp [r, aoCirInverseHistoryDiscount]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hc0 : 0 ≤ 1 - r := by linarith
  have hseries := aoCir_inverse_profile_depth_series_bound M.gamma q j hγsmall hq48
  have hprofileNonneg (d : ℕ) : 0 ≤ profileTerm d := by
    dsimp [profileTerm]
    unfold orderInverseProfile
    positivity
  have hprofileSummable : Summable (fun d : ℕ => r ^ d * profileTerm d) := by
    simpa only [r, profileTerm, aoCirInverseHistoryDiscount, mul_assoc] using hseries.1
  let F : ℕ → Cutoff.CutoffSample 2 → ℝ := fun d ω =>
    ((1 - r) * r ^ d) * aoCirResetInverseDepthMax M Q (j + d) N Q.scale q t ω
  have hFmeas : ∀ d, Measurable (F d) := by
    intro d
    change Measurable (fun ω => ((1 - r) * r ^ d) *
      aoCirResetInverseDepthMax M Q (j + d) N Q.scale q t ω)
    exact measurable_const.mul
      (aoCir_reset_inverse_depth_max_measurable M Q (j + d) N Q.scale q t)
  have hdepth (d : ℕ) :
      eLpNorm (aoCirResetInverseDepthMax M Q (j + d) N Q.scale q t)
          (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (profileTerm d) := by
    have hpop := aoCir_reset_inverse_depth_population_bound reset M h hM hγ hγsmall
      hstate Q N hQN (j + d) q hq48 t ht0 ht1
    have hmaxNonneg := aoCir_reset_inverse_depth_max_nonneg M Q (j + d) N Q.scale q t
    change eLpNorm (ENNReal.ofReal ∘
      fun ω => aoCirResetInverseDepthMax M Q (j + d) N Q.scale q t ω)
        (ENNReal.ofReal q) μ ≤ _ at hpop
    rw [eLpNorm_ofReal _ (Filter.Eventually.of_forall hmaxNonneg)] at hpop
    have hfactor := aoCir_descendant_population_factor Q j d q
    rw [hfactor] at hpop
    have hpow : 0 ≤ Real.rpow 9 (((j + d : ℕ) : ℝ) / q) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      _ ≤ ENNReal.ofReal (Real.rpow 9 (((j + d : ℕ) : ℝ) / q)) *
          ENNReal.ofReal (orderInverseProfile (153 / 100) M.gamma q
            (((j + d : ℕ) : ℝ) + 1)) := hpop
      _ = ENNReal.ofReal (Real.rpow 9 (((j + d : ℕ) : ℝ) / q) *
          orderInverseProfile (153 / 100) M.gamma q
            (((j + d : ℕ) : ℝ) + 1)) := (ENNReal.ofReal_mul hpow).symm
      _ = ENNReal.ofReal (profileTerm d) := rfl
  have hterm (d : ℕ) :
      eLpNorm (F d) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((1 - r) * r ^ d * profileTerm d) := by
    have hcoef : 0 ≤ (1 - r) * r ^ d := mul_nonneg hc0 (pow_nonneg hr0 d)
    have heq : F d = ((1 - r) * r ^ d) •
        aoCirResetInverseDepthMax M Q (j + d) N Q.scale q t := by
      funext ω
      simp [F, smul_eq_mul]
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal hcoef]
    calc
      _ ≤ ENNReal.ofReal ((1 - r) * r ^ d) * ENNReal.ofReal (profileTerm d) :=
        mul_le_mul_of_nonneg_left (hdepth d) bot_le
      _ = _ := by rw [← ENNReal.ofReal_mul hcoef]
  have hbudgetSummable : Summable (fun d : ℕ => (1 - r) * (r ^ d * profileTerm d)) :=
    hprofileSummable.mul_left (1 - r)
  have hbudget : (∑' d : ℕ, eLpNorm (F d) (ENNReal.ofReal q) μ) ≤
      ENNReal.ofReal ((1 - r) * ∑' d : ℕ, r ^ d * profileTerm d) := by
    calc
      _ ≤ ∑' d : ℕ, ENNReal.ofReal ((1 - r) * r ^ d * profileTerm d) :=
        ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal ((1 - r) * ∑' d : ℕ, r ^ d * profileTerm d) := by
        calc
          _ = ∑' d : ℕ, ENNReal.ofReal ((1 - r) * (r ^ d * profileTerm d)) := by
            apply tsum_congr
            intro d
            congr 1
            ring
          _ = ENNReal.ofReal ((1 - r) * ∑' d : ℕ, r ^ d * profileTerm d) := by
            rw [← ENNReal.ofReal_tsum_of_nonneg (fun d =>
              mul_nonneg hc0 (mul_nonneg (pow_nonneg hr0 d) (hprofileNonneg d)))
              hbudgetSummable]
            rw [tsum_mul_left]
  have hfinite : (∑' d : ℕ, eLpNorm (F d) (ENNReal.ofReal q) μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget
  have hsumLp := Inverse.eLpNorm_tsum_le_of_finite μ (ENNReal.ofReal q) hqENN
    F hFmeas hfinite
  have hseriesEq :
      (fun ω => aoCirResetInverseDepthProfileSeries M Q j N q t ω) =
        fun ω => ∑' d : ℕ, F d ω := by
    funext ω
    simp only [aoCirResetInverseDepthProfileSeries, F, r,
      aoCirInverseHistoryDiscount]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro d
    ring
  change eLpNorm (fun ω => aoCirResetInverseDepthProfileSeries M Q j N q t ω)
      (ENNReal.ofReal q) μ ≤ _
  rw [hseriesEq]
  calc
    _ ≤ ∑' d : ℕ, eLpNorm (F d) (ENNReal.ofReal q) μ := hsumLp
    _ ≤ ENNReal.ofReal ((1 - r) *
          ∑' d : ℕ, r ^ d * profileTerm d) := hbudget
    _ ≤ ENNReal.ofReal (aoCirInverseHistoryFactor M.gamma *
          Real.rpow 9 ((j : ℝ) / q) *
          orderInverseProfile (153 / 100) M.gamma q ((j : ℝ) + 1)) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [r, profileTerm, aoCirInverseHistoryDiscount, mul_assoc] using hseries.2

end
end ASDExplicitGamma.AllOrder
