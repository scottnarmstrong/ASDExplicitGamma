module

public import ASDExplicitGamma.Inverse.SourceInterfaceEnergy

/-! Complete old-history mean and common-center transport, keeping the actual
cutoff law and OLD true frame through the infinite depth passage. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory Algsuperdiff.Section3 Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Native
open scoped ENNReal

noncomputable section

private theorem in_source_old_energy_history_weight_pos
    (M : ABKModel 2) (r : ℕ) :
    0 < inSourceOldEnergyHistoryWeight M r := by
  have hα := Scalar.inverse_history_discount_range
  have hpref : 0 < 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  have hpow : 0 < Scalar.inverseHistoryDiscount ^ (2 * r) :=
    pow_pos hα.1 _
  have hscale : 0 < (3 : ℝ) ^ (2 * M.gamma * (r : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  unfold inSourceOldEnergyHistoryWeight
  exact mul_pos (mul_pos (mul_pos hpref hpow) (by norm_num)) hscale

/-- The OLD weak row at depth zero contains the complete weighted endpoint
mean history. Its rare term is retained in the source row and discarded only
by positivity after the history is identified. -/
theorem in_source_complete_old_endpoint_mean_history
    (M : ABKModel 2) (m : ℤ) (hSmall : NativeSourceSmallerGammaBounds M m) :
    Summable (fun r : ℕ =>
      inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal) ∧
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal) ≤
      (nativeCompletedSourceWeak M m 0).toReal := by
  let α := Scalar.inverseHistoryDiscount
  let c := ENNReal.ofReal (1 - α ^ 2)
  let c0 := ENNReal.ofReal (3683 / 2500 : ℝ)
  let qweight : ℕ → ℝ := fun r => α ^ (2 * r) *
    (3 : ℝ) ^ (2 * M.gamma * (r : ℝ))
  let F : ℕ → ℝ≥0∞ := fun r => ENNReal.ofReal (qweight r) *
    (c0 * nativeCompletedSourceMean M m r +
      ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
        eLpNorm (cutoffTraceDefect M m (m - (r : ℤ))) 20
          (Cutoff.cutoffSampleLaw M).toMeasure)
  let G : ℕ → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (inSourceOldEnergyHistoryWeight M r) *
      nativeCompletedSourceMean M m r
  have hα := Scalar.inverse_history_discount_range
  have hfactor : 0 < 1 - α ^ 2 := by nlinarith [hα.1, hα.2]
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr hfactor).ne'
  have hqweightPos (r : ℕ) : 0 < qweight r := by
    dsimp [qweight]
    exact mul_pos (pow_pos hα.1 _) (Real.rpow_pos_of_pos (by norm_num) _)
  have hweightPos (r : ℕ) : 0 < inSourceOldEnergyHistoryWeight M r :=
    in_source_old_energy_history_weight_pos M r
  have hweightCast (r : ℕ) :
      ENNReal.ofReal (inSourceOldEnergyHistoryWeight M r) =
        c * (ENNReal.ofReal (qweight r) * c0) := by
    have hreal : inSourceOldEnergyHistoryWeight M r =
        (1 - α ^ 2) * (qweight r * (3683 / 2500 : ℝ)) := by
      dsimp [inSourceOldEnergyHistoryWeight, qweight, α]
      ring
    rw [hreal, ENNReal.ofReal_mul hfactor.le,
      ENNReal.ofReal_mul (hqweightPos r).le]
  have hrareNonneg (r : ℕ) :
      0 ≤ ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
        eLpNorm (cutoffTraceDefect M m (m - (r : ℤ))) 20
          (Cutoff.cutoffSampleLaw M).toMeasure := by positivity
  have hterm (r : ℕ) : G r ≤ c * F r := by
    change ENNReal.ofReal (inSourceOldEnergyHistoryWeight M r) *
      nativeCompletedSourceMean M m r ≤ c * F r
    rw [hweightCast]
    change c * (ENNReal.ofReal (qweight r) * c0) *
        nativeCompletedSourceMean M m r ≤
      c * (ENNReal.ofReal (qweight r) *
        (c0 * nativeCompletedSourceMean M m r +
          ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
            eLpNorm (cutoffTraceDefect M m (m - (r : ℤ))) 20
              (Cutoff.cutoffSampleLaw M).toMeasure))
    calc
      _ = c * (ENNReal.ofReal (qweight r) *
          (c0 * nativeCompletedSourceMean M m r)) := by simp [mul_assoc]
      _ ≤ c * (ENNReal.ofReal (qweight r) *
          (c0 * nativeCompletedSourceMean M m r +
            ENNReal.ofReal (3 / 10 ^ 46 : ℝ) *
              eLpNorm (cutoffTraceDefect M m (m - (r : ℤ))) 20
                (Cutoff.cutoffSampleLaw M).toMeasure)) := by
          gcongr
          exact le_add_of_nonneg_right (hrareNonneg r)
  have hweak0 := hSmall.weak (⟨0, by omega⟩ : Fin 6)
  have hweakEq : nativeCompletedSourceWeak M m 0 = c * ∑' r : ℕ, F r := by
    simp [nativeCompletedSourceWeak, c, F, qweight, c0, α]
  have hsumle : (∑' r : ℕ, G r) ≤ nativeCompletedSourceWeak M m 0 := by
    calc
      (∑' r : ℕ, G r) ≤ ∑' r : ℕ, c * F r := ENNReal.tsum_le_tsum hterm
      _ = c * ∑' r : ℕ, F r := ENNReal.tsum_mul_left
      _ = nativeCompletedSourceWeak M m 0 := hweakEq.symm
  have hsumBound : (∑' r : ℕ, G r) ≤ nativeCompletedSourceWeak M m 0 := hsumle
  have hweakNe : nativeCompletedSourceWeak M m 0 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hweak0
  have hsumNe : (∑' r : ℕ, G r) ≠ ⊤ :=
    lt_top_iff_ne_top.mp (lt_of_le_of_lt hsumBound (lt_top_iff_ne_top.mpr hweakNe))
  have hGtermNe (r : ℕ) : G r ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top hsumNe r
  have hGtoReal (r : ℕ) : (G r).toReal =
      inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal := by
    have hμne : nativeCompletedSourceMean M m r ≠ ⊤ := by
      by_contra htop
      have htop' : nativeCompletedSourceMean M m r = ⊤ := by simpa using htop
      apply hGtermNe r
      change ENNReal.ofReal (inSourceOldEnergyHistoryWeight M r) *
        nativeCompletedSourceMean M m r = ⊤
      rw [htop', ENNReal.mul_eq_top]
      exact Or.inl ⟨(ENNReal.ofReal_pos.mpr (hweightPos r)).ne', rfl⟩
    change (ENNReal.ofReal (inSourceOldEnergyHistoryWeight M r) *
      nativeCompletedSourceMean M m r).toReal = _
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hweightPos r).le]
  have hseriesG : Summable (fun r : ℕ => (G r).toReal) := ENNReal.summable_toReal hsumNe
  have hseries : Summable (fun r : ℕ =>
      inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal) := by
    apply hseriesG.congr
    intro r
    exact hGtoReal r
  have hrealSum :
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal) = (∑' r : ℕ, G r).toReal := by
    calc
      _ = ∑' r : ℕ, (G r).toReal := by
        apply tsum_congr
        intro r
        exact (hGtoReal r).symm
      _ = _ := (ENNReal.tsum_toReal_eq
        (fun r => ENNReal.ne_top_of_tsum_ne_top hsumNe r)).symm
  refine ⟨hseries, ?_⟩
  rw [hrealSum]
  exact ENNReal.toReal_mono hweakNe hsumle

/-- The expected trace during insertion is nonnegative in the actual cutoff
law, since every partially inserted coefficient remains in the true
ellipticity class. -/
theorem in_source_actual_mean_nonneg
    (M : ABKModel 2) (m : ℤ) (r : ℕ) (t : ℝ) :
    0 ≤ inSourceMeanActual M m r t := by
  let q := m - (r : ℤ)
  change 0 ≤ modelTraceHeatAverage q M m t
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) :=
    (Annealed.sigmaBar_characterization M m).1
  unfold modelTraceHeatAverage
  apply integral_nonneg
  intro ω
  change 0 ≤ traceDefect (cubeSet (originCube 2 q))
    (Model.partialInsertedCoefficient M m t ω).toFun
    (Annealed.sigmaBar M m : ℝ)
  rw [← modelTraceObservable_inserted_eq_traceDefect q M ell m hK
    (Annealed.sigmaBar M m : ℝ) t ω]
  exact modelTraceObservable_nonneg q M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos hσ _

/-- Complete common-center transport at time `t`: the actual weighted source
means are summable, and their whole OLD-history sum is controlled by the
completed endpoint history plus the complete state-derived energy series. -/
theorem in_source_actual_complete_common_center_transport_by_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j)
    (hSmall : NativeSourceSmallerGammaBounds M m)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun r : ℕ => inSourceOldEnergyHistoryWeight M r *
      inSourceMeanActual M m r t) ∧
    (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
      inSourceMeanActual M m r t) ≤
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal) +
      t * (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        inSourceOldEnergyCap M h m r) := by
  have hEndpoint := in_source_complete_old_endpoint_mean_history M m hSmall
  have hEnergy := in_source_actual_complete_old_energy_sum M h hM hg m hpast
  have hCap := in_source_actual_weighted_old_energy_cap_summable M h hM hg m hpast
  have hMajorant : Summable (fun r : ℕ =>
      inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal +
      t * (inSourceOldEnergyHistoryWeight M r *
        inSourceOldEnergyCap M h m r)) := by
    exact hEndpoint.1.add (hCap.mul_left t)
  have hpoint (r : ℕ) :
      inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t ≤
        inSourceOldEnergyHistoryWeight M r *
          (nativeCompletedSourceMean M m r).toReal +
          t * (inSourceOldEnergyHistoryWeight M r *
            inSourceOldEnergyCap M h m r) := by
    have htransport := in_source_actual_mean_transport_old_energy
      M h hM hg m hpast r t ht
    have hweight : 0 ≤ inSourceOldEnergyHistoryWeight M r := by
      exact le_of_lt (by
        exact in_source_old_energy_history_weight_pos M r)
    calc
      _ ≤ inSourceOldEnergyHistoryWeight M r *
          ((nativeCompletedSourceMean M m r).toReal +
            t * inSourceOldEnergyCap M h m r) :=
        mul_le_mul_of_nonneg_left htransport.1 hweight
      _ = _ := by ring
  have hnonneg (r : ℕ) :
      0 ≤ inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t :=
    mul_nonneg (le_of_lt (in_source_old_energy_history_weight_pos M r))
      (in_source_actual_mean_nonneg M m r t)
  have hseries := Summable.of_nonneg_of_le hnonneg hpoint hMajorant
  have hsum := hseries.tsum_le_tsum hpoint hMajorant
  have hsumEq :
      (∑' r : ℕ, (inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal +
        t * (inSourceOldEnergyHistoryWeight M r *
          inSourceOldEnergyCap M h m r))) =
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        (nativeCompletedSourceMean M m r).toReal) +
        t * (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
          inSourceOldEnergyCap M h m r) := by
    rw [hEndpoint.1.tsum_add (hCap.mul_left t), tsum_mul_left]
  exact ⟨hseries, hsum.trans_eq hsumEq⟩

end
end ASDExplicitGamma.Inverse
