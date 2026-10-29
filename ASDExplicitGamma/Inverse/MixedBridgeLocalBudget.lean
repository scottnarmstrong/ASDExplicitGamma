module

public import ASDExplicitGamma.Inverse.SourceRows
public import ASDExplicitGamma.Inverse.SourceEnergy
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Numerics.Native.Source5

/-! The exact depth-five source budget for translated OLD-Theta cells. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar
open scoped ENNReal

noncomputable section

/-- The local-cell OLD chronology weights.  Their source means and slopes
are indexed by `5+j`, while the weights restart at the local cell. -/
def mixedBridgeLocalWeight (M : ABKModel 2) (j : ℕ) : ℝ :=
  (1 - Scalar.inverseHistoryDiscount ^ 2) *
    Scalar.inverseHistoryDiscount ^ (2 * j) *
      mixedBridgeOldInverseBaseline M j

/-- The actual shifted OLD slope series for a source cell of scale `m-5`. -/
def mixedBridgeLocalSlope (M : ABKModel 2) (h : ℝ) (m : ℤ) : ℝ :=
  ∑' j : ℕ, mixedBridgeLocalWeight M j *
    inSourceMeanSlopeActual M h m (5 + j)

/-- Exact five-level weight shift. -/
theorem mixed_bridge_local_weight_shift (M : ABKModel 2) (j : ℕ) :
    inSourceOldEnergyHistoryWeight M (5 + j) =
      ((Scalar.inverseHistoryDiscount ^ 10) *
        (3 : ℝ) ^ (10 * M.gamma)) * mixedBridgeLocalWeight M j := by
  unfold inSourceOldEnergyHistoryWeight mixedBridgeLocalWeight
    mixedBridgeOldInverseBaseline
  rw [show 2 * (5 + j : ℕ) = 10 + 2 * j by omega, pow_add]
  have hrpow :
      (3 : ℝ) ^ (2 * M.gamma * ((5 + j : ℕ) : ℝ)) =
        (3 : ℝ) ^ (10 * M.gamma) *
          (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
    rw [show 2 * M.gamma * ((5 + j : ℕ) : ℝ) =
      10 * M.gamma + 2 * M.gamma * (j : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  rw [hrpow]
  ring

private theorem mixed_bridge_local_weight_nonneg
    (M : ABKModel 2) (j : ℕ) : 0 ≤ mixedBridgeLocalWeight M j := by
  unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
  have hα := Scalar.inverse_history_discount_range
  have hpref : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  exact mul_nonneg (mul_nonneg hpref
      (pow_nonneg hα.1.le _))
    (mul_nonneg (by norm_num : 0 ≤ (3683 / 2500 : ℝ))
      (Real.rpow_nonneg (by norm_num) _))

/-- The shifted actual slope is summable, and its value is bounded by the
exact five-level factor times the root actual-slope series. -/
theorem mixed_bridge_local_slope_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    Summable (fun j : ℕ => mixedBridgeLocalWeight M j *
      inSourceMeanSlopeActual M h m (5 + j)) ∧
    mixedBridgeLocalSlope M h m ≤
      (((Scalar.inverseHistoryDiscount ^ 10) *
        (3 : ℝ) ^ (10 * M.gamma))⁻¹) * mixedXiSlope M h m := by
  let a : ℕ → ℝ := fun r =>
    inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r
  let D : ℝ := (Scalar.inverseHistoryDiscount ^ 10) *
    (3 : ℝ) ^ (10 * M.gamma)
  have hpastM : ∀ l < m, nativeInductionState M h l :=
    fun l hl => hpast l (hl.trans hm)
  have hroot := in_source_actual_complete_old_energy_sum
    M h hM hγ m hpastM
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (pow_pos Scalar.inverse_history_discount_range.1 _) 
      (Real.rpow_pos_of_pos (by norm_num) _)
  have hshift (j : ℕ) :
      a (5 + j) = D *
        (mixedBridgeLocalWeight M j *
          inSourceMeanSlopeActual M h m (5 + j)) := by
    dsimp [a, D]
    rw [mixed_bridge_local_weight_shift]
    ring
  have htail : Summable (fun j : ℕ => a (5 + j)) :=
    hroot.1.comp_injective (fun i j hij => by omega)
  have hlocal : Summable (fun j : ℕ => mixedBridgeLocalWeight M j *
      inSourceMeanSlopeActual M h m (5 + j)) := by
    have hscaled := htail.mul_left D⁻¹
    apply hscaled.congr
    intro j
    rw [hshift]
    field_simp
  have htail_eq :
      (∑' j : ℕ, a (5 + j)) =
        D * ∑' j : ℕ,
          mixedBridgeLocalWeight M j *
            inSourceMeanSlopeActual M h m (5 + j) := by
    calc
      _ = ∑' j : ℕ, D *
          (mixedBridgeLocalWeight M j *
            inSourceMeanSlopeActual M h m (5 + j)) := by
          apply tsum_congr
          exact hshift
      _ = _ := tsum_mul_left
  have hroot_eq :
      (∑' r : ℕ, a r) = (∑ r ∈ Finset.range 5, a r) +
        ∑' j : ℕ, a (5 + j) := by
    simpa [Finset.sum_range_succ, Nat.add_comm] using
      (hroot.1.sum_add_tsum_nat_add 5).symm
  have hprefix : 0 ≤ ∑ r ∈ Finset.range 5, a r := by
    apply Finset.sum_nonneg
    intro r hr
    have hweight : 0 ≤ inSourceOldEnergyHistoryWeight M r := by
      unfold inSourceOldEnergyHistoryWeight
      have hα := Scalar.inverse_history_discount_range
      have hpref : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
        nlinarith [hα.1, hα.2]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg hpref (pow_nonneg hα.1.le _))
          (by norm_num : 0 ≤ (3683 / 2500 : ℝ)))
        (Real.rpow_nonneg (by norm_num) _)
    have hslope : 0 ≤ inSourceMeanSlopeActual M h m r := by
      unfold inSourceMeanSlopeActual
      exact le_max_left _ _
    exact mul_nonneg hweight hslope
  have htail_le : (∑' j : ℕ, a (5 + j)) ≤ ∑' r : ℕ, a r := by
    rw [hroot_eq]
    linarith
  have hDinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hD.le
  have hlocal_eq :
      (∑' j : ℕ,
        mixedBridgeLocalWeight M j *
          inSourceMeanSlopeActual M h m (5 + j)) =
        D⁻¹ * ∑' j : ℕ, a (5 + j) := by
    rw [htail_eq]
    field_simp [ne_of_gt hD]
  have hmain :
      (∑' j : ℕ,
        mixedBridgeLocalWeight M j *
          inSourceMeanSlopeActual M h m (5 + j)) ≤
        D⁻¹ * ∑' r : ℕ, a r := by
    have hmul := mul_le_mul_of_nonneg_left htail_le hDinv
    calc
      _ = D⁻¹ * (∑' j : ℕ, a (5 + j)) := by
        exact hlocal_eq
      _ ≤ _ := hmul
  refine ⟨hlocal, ?_⟩
  change (∑' j : ℕ,
      mixedBridgeLocalWeight M j *
        inSourceMeanSlopeActual M h m (5 + j)) ≤ _
  simpa [mixedXiSlope, a, D, mul_inv] using hmain

/-- The completed depth-five weak endpoint controls the exact local baseline
series, before the insertion-time transport. -/
theorem mixed_bridge_local_completed_weak_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    Summable (fun j : ℕ => mixedBridgeLocalWeight M j *
      (nativeCompletedSourceMean M m (5 + j)).toReal) ∧
    (∑' j : ℕ, mixedBridgeLocalWeight M j *
      (nativeCompletedSourceMean M m (5 + j)).toReal) ≤
        mixedXiPreCap M := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let c := ENNReal.ofReal (1 - α ^ 2)
  let c0 := ENNReal.ofReal (3683 / 2500 : ℝ)
  let qweight : ℕ → ℝ := fun j => α ^ (2 * j) *
    (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))
  let F : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (qweight j) *
    (c0 * nativeCompletedSourceMean M m (5 + j) +
      ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
        eLpNorm (cutoffTraceDefect M m (m - ((5 + j : ℕ) : ℤ))) 20 μ)
  let G : ℕ → ℝ≥0∞ := fun j =>
    ENNReal.ofReal (mixedBridgeLocalWeight M j) *
      nativeCompletedSourceMean M m (5 + j)
  have hα := Scalar.inverse_history_discount_range
  have hfac : 0 < 1 - α ^ 2 := by nlinarith [hα.1, hα.2]
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr hfac).ne'
  have hqpos (j : ℕ) : 0 < qweight j := by
    dsimp [qweight]
    exact mul_pos (pow_pos hα.1 _) (Real.rpow_pos_of_pos (by norm_num) _)
  have hwpos (j : ℕ) : 0 < mixedBridgeLocalWeight M j := by
    unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
    exact mul_pos
      (mul_pos (by linarith [hfac]) (pow_pos hα.1 _))
      (mul_pos (by norm_num : 0 < (3683 / 2500 : ℝ))
        (Real.rpow_pos_of_pos (by norm_num) _))
  have hweightCast (j : ℕ) :
      ENNReal.ofReal (mixedBridgeLocalWeight M j) =
        c * (ENNReal.ofReal (qweight j) * c0) := by
    have hreal : mixedBridgeLocalWeight M j =
        (1 - α ^ 2) * (qweight j * (3683 / 2500 : ℝ)) := by
      unfold mixedBridgeLocalWeight mixedBridgeOldInverseBaseline
      dsimp [qweight]
      ring
    rw [hreal, ENNReal.ofReal_mul hfac.le,
      ENNReal.ofReal_mul (hqpos j).le]
  have hweak := in_source_rows M h hM hγ N hpast m hm
  have hweakBound : nativeCompletedSourceWeak M m 5 ≤
      ENNReal.ofReal (mixedXiPreCap M) := by
    simpa [mixedXiPreCap] using hweak.2.2.2.1
  have hweakEq : nativeCompletedSourceWeak M m 5 = c * ∑' j : ℕ, F j := by
    simp [nativeCompletedSourceWeak, c, F, qweight, c0, α, μ]
  have hrare0 (j : ℕ) :
      0 ≤ ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
        eLpNorm (cutoffTraceDefect M m (m - ((5 + j : ℕ) : ℤ))) 20 μ := by
    positivity
  have hterm (j : ℕ) : G j ≤ c * F j := by
    change ENNReal.ofReal (mixedBridgeLocalWeight M j) *
      nativeCompletedSourceMean M m (5 + j) ≤ c * F j
    rw [hweightCast j]
    change c * (ENNReal.ofReal (qweight j) * c0) *
        nativeCompletedSourceMean M m (5 + j) ≤
      c * (ENNReal.ofReal (qweight j) *
        (c0 * nativeCompletedSourceMean M m (5 + j) +
          ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
            eLpNorm (cutoffTraceDefect M m (m - ((5 + j : ℕ) : ℤ))) 20 μ))
    calc
      _ = c * (ENNReal.ofReal (qweight j) *
          (c0 * nativeCompletedSourceMean M m (5 + j))) := by simp [mul_assoc]
      _ ≤ c * (ENNReal.ofReal (qweight j) *
          (c0 * nativeCompletedSourceMean M m (5 + j) +
            ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
              eLpNorm (cutoffTraceDefect M m (m - ((5 + j : ℕ) : ℤ))) 20 μ)) := by
          gcongr
          exact le_add_of_nonneg_right (hrare0 j)
  have hsumle : (∑' j : ℕ, G j) ≤ nativeCompletedSourceWeak M m 5 := by
    calc
      _ ≤ ∑' j : ℕ, c * F j := ENNReal.tsum_le_tsum hterm
      _ = c * ∑' j : ℕ, F j := ENNReal.tsum_mul_left
      _ = nativeCompletedSourceWeak M m 5 := hweakEq.symm
  have hweakNe : nativeCompletedSourceWeak M m 5 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hweakBound
  have hsumNe : (∑' j : ℕ, G j) ≠ ⊤ := by
    exact lt_top_iff_ne_top.mp
      (lt_of_le_of_lt hsumle (lt_top_iff_ne_top.mpr hweakNe))
  have hGtermNe (j : ℕ) : G j ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top hsumNe j
  have hGtoReal (j : ℕ) : (G j).toReal =
      mixedBridgeLocalWeight M j *
        (nativeCompletedSourceMean M m (5 + j)).toReal := by
    have hμne : nativeCompletedSourceMean M m (5 + j) ≠ ⊤ := by
      intro htop
      apply hGtermNe j
      change ENNReal.ofReal (mixedBridgeLocalWeight M j) *
        nativeCompletedSourceMean M m (5 + j) = ⊤
      rw [htop, ENNReal.mul_eq_top]
      exact Or.inl ⟨(ENNReal.ofReal_pos.mpr (hwpos j)).ne', rfl⟩
    change (ENNReal.ofReal (mixedBridgeLocalWeight M j) *
      nativeCompletedSourceMean M m (5 + j)).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwpos j).le]
  have hseriesG : Summable (fun j : ℕ => (G j).toReal) :=
    ENNReal.summable_toReal hsumNe
  have hseries : Summable (fun j : ℕ =>
      mixedBridgeLocalWeight M j *
        (nativeCompletedSourceMean M m (5 + j)).toReal) := by
    apply hseriesG.congr
    intro j
    exact hGtoReal j
  have hrealSum :
      (∑' j : ℕ, mixedBridgeLocalWeight M j *
        (nativeCompletedSourceMean M m (5 + j)).toReal) =
        (∑' j : ℕ, G j).toReal := by
    calc
      _ = ∑' j : ℕ, (G j).toReal := by
        apply tsum_congr
        intro j
        exact (hGtoReal j).symm
      _ = _ := (ENNReal.tsum_toReal_eq
        (fun j => ENNReal.ne_top_of_tsum_ne_top hsumNe j)).symm
  have htheta0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hxi0 : 0 ≤ (inSourceXi5Pre : ℝ) := by
    norm_num [inSourceXi5Pre,
      ASDExplicitGamma.Numerics.Native.nativeSource5Result]
  have hcap0 : 0 ≤ mixedXiPreCap M := by
    unfold mixedXiPreCap
    exact mul_nonneg htheta0 hxi0
  refine ⟨hseries, ?_⟩
  rw [hrealSum]
  calc
    (∑' j : ℕ, G j).toReal ≤ (nativeCompletedSourceWeak M m 5).toReal :=
      ENNReal.toReal_mono hweakNe hsumle
    _ ≤ mixedXiPreCap M := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hweakBound
      simpa [ENNReal.toReal_ofReal hcap0] using hh

/-- Source-faithful transport of the local OLD mean history. The actual
slopes remain at indices `5+j`; only the endpoint is simplified by the
completed weak row. -/
theorem mixed_bridge_local_mean_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun j : ℕ => mixedBridgeLocalWeight M j *
      inSourceMeanActual M m (5 + j) t) ∧
    (∑' j : ℕ, mixedBridgeLocalWeight M j *
      inSourceMeanActual M m (5 + j) t) ≤
      mixedXiPreCap M + t * mixedBridgeLocalSlope M h m := by
  let f : ℕ → ℝ := fun j =>
    mixedBridgeLocalWeight M j * inSourceMeanActual M m (5 + j) t
  let g : ℕ → ℝ := fun j =>
    mixedBridgeLocalWeight M j *
      (nativeCompletedSourceMean M m (5 + j)).toReal
  let s : ℕ → ℝ := fun j => mixedBridgeLocalWeight M j *
    inSourceMeanSlopeActual M h m (5 + j)
  have hend := mixed_bridge_local_completed_weak_endpoint
    M h hM hγ N hpast m hm
  have hslope := mixed_bridge_local_slope_transport
    M h hM hγ N hpast m hm
  have htransport (j : ℕ) : f j ≤ g j + t * s j := by
    change mixedBridgeLocalWeight M j *
        inSourceMeanActual M m (5 + j) t ≤
      mixedBridgeLocalWeight M j *
          (nativeCompletedSourceMean M m (5 + j)).toReal +
        t * (mixedBridgeLocalWeight M j *
          inSourceMeanSlopeActual M h m (5 + j))
    have htMean := in_source_actual_mean_transport_by_slope M h hM m
      (5 + j) t ht
    calc
      _ ≤ mixedBridgeLocalWeight M j *
          (inSourceMeanActual M m (5 + j) 0 +
            t * inSourceMeanSlopeActual M h m (5 + j)) :=
        mul_le_mul_of_nonneg_left htMean
          (mixed_bridge_local_weight_nonneg M j)
      _ = mixedBridgeLocalWeight M j *
          (nativeCompletedSourceMean M m (5 + j)).toReal +
            t * (mixedBridgeLocalWeight M j *
              inSourceMeanSlopeActual M h m (5 + j)) := by
          rw [← in_source_mean_old_endpoint M m (5 + j)]
          ring
  have hnonnegSlope (j : ℕ) : 0 ≤ s j := by
    dsimp [s]
    exact mul_nonneg (mixed_bridge_local_weight_nonneg M j)
      (show 0 ≤ inSourceMeanSlopeActual M h m (5 + j) from by
        unfold inSourceMeanSlopeActual; exact le_max_left _ _)
  have hsumSlope := hslope.1
  have hmajorant := hend.1.add (hsumSlope.mul_left t)
  have hsumf : Summable f :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (mixed_bridge_local_weight_nonneg M j)
        (in_source_actual_mean_nonneg M m (5 + j) t))
      htransport hmajorant
  have hsumBound := hsumf.tsum_le_tsum htransport hmajorant
  have hsumIdentity :
      (∑' j : ℕ, (g j + t * s j)) =
        (∑' j : ℕ, g j) + t * ∑' j : ℕ, s j := by
    rw [hend.1.tsum_add (hsumSlope.mul_left t), tsum_mul_left]
  refine ⟨hsumf, ?_⟩
  have hsumBound' : (∑' j : ℕ, f j) ≤
      (∑' j : ℕ, g j) + t * ∑' j : ℕ, s j := by
    simpa [hsumIdentity] using hsumBound
  have hmain : ∑' j : ℕ, g j ≤ mixedXiPreCap M := hend.2
  have hlocalSlope : ∑' j : ℕ, s j = mixedBridgeLocalSlope M h m := by
    rfl
  rw [hlocalSlope] at hsumBound'
  linarith

end

end ASDExplicitGamma.Inverse
