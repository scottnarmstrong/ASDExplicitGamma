module

public import ASDExplicitGamma.Inverse.SourceEnergy
public import ASDExplicitGamma.Inverse.ParentGapEnergyInputs

/-! The actual OLD-slope scalar series consumed by the parent-gap assembly.
The root weak endpoint is compared to the carried depth-five budget explicitly;
the transported slope is never replaced by its larger cap series. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Native ASDExplicitGamma.Numerics.Native
noncomputable section

private theorem parent_gap_weight_nonneg (M : ABKModel 2) (j : ℕ) :
    0 ≤ inSourceOldEnergyHistoryWeight M j := by
  have ha := Scalar.inverse_history_discount_range
  have hc : 0 ≤ 1-Scalar.inverseHistoryDiscount^2 := by
    nlinarith [ha.1,ha.2]
  unfold inSourceOldEnergyHistoryWeight
  exact mul_nonneg (mul_nonneg (mul_nonneg hc (pow_nonneg ha.1.le _)) (by norm_num))
    (Real.rpow_nonneg (by norm_num) _)

private theorem parent_gap_root_weak_row_le_five :
    nativeCompletedWeakRows.getD 0 0 ≤ inSourceXi5Pre := by
  have hrow : nativeCompletedWeakRows.getD 0 0=nativeSource0Result.2 := by
    simp [nativeCompletedWeakRows]
  have hsmall : nativeCompletedWeakRows.getD 0 0 ≤ (13/100:ℚ) := by
    rw [hrow]
    exact nativeSource0_caps.2.2.1.le.trans (by norm_num)
  exact hsmall.trans (by norm_num [inSourceXi5Pre,nativeSource5Result])

/-- The actual root completed weak row lies below the bridge's sharp carried
xi5 budget by an explicit certified row0-to-row5 comparison. This does not
project a depth-five source estimate onto the wrong observable. -/
theorem parent_gap_root_weak_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    (nativeCompletedSourceWeak M m 0).toReal ≤ mixedBridgeXiPre M := by
  have hs := native_source_smaller_gamma M h hM hg N hpast m hm
  have hrow := hs.weak (0 : Fin 6)
  change nativeCompletedSourceWeak M m 0 ≤
    ENNReal.ofReal (theta M*((nativeCompletedWeakRows.getD 0 0:ℚ):ℝ)) at hrow
  have htheta : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hnum : ((nativeCompletedWeakRows.getD 0 0:ℚ):ℝ) ≤ (inSourceXi5Pre:ℝ) := by
    exact_mod_cast parent_gap_root_weak_row_le_five
  have hbound : nativeCompletedSourceWeak M m 0 ≤ ENNReal.ofReal (mixedBridgeXiPre M) :=
    hrow.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hnum htheta))
  have hpre : 0 ≤ mixedBridgeXiPre M := by
    unfold mixedBridgeXiPre
    apply mul_nonneg htheta
    norm_num [inSourceXi5Pre,nativeSource5Result]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hpre)

/-- The complete actual-law weighted source trace series is summable and
bounded by the completed bridge budget plus the ACTUAL OLD slope series.
All source-row and energy inputs are consumed internally under the outer-N
native chronology; no energy, slope, cap or endpoint estimate is a premise. -/
theorem parent_gap_source_trace_history_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Summable (fun j : ℕ => inSourceOldEnergyHistoryWeight M j *
      inSourceMeanActual M m j t) ∧
    (∑' j : ℕ,inSourceOldEnergyHistoryWeight M j * inSourceMeanActual M m j t) ≤
      mixedBridgeXiPre M+t*mixedBridgeXiSlope M h m := by
  have hs := native_source_smaller_gamma M h hM hg N hpast m hm
  have htransport := in_source_transport M h hM hg N hpast m hm
  have henergy := in_source_energy M h hM hg N hpast m hm
  have hendpoint := in_source_complete_old_endpoint_mean_history M m hs
  have hslope := henergy.2.2.1.1
  have hmajorant := hendpoint.1.add (hslope.mul_left t)
  have hpoint (j : ℕ) :
      inSourceOldEnergyHistoryWeight M j * inSourceMeanActual M m j t ≤
      inSourceOldEnergyHistoryWeight M j*(nativeCompletedSourceMean M m j).toReal+
        t*(inSourceOldEnergyHistoryWeight M j*inSourceMeanSlopeActual M h m j) := by
    have hpanel := mul_le_mul_of_nonneg_left (htransport.1 j t ht)
      (parent_gap_weight_nonneg M j)
    rw [htransport.2.1 j] at hpanel
    exact hpanel.trans_eq (by ring)
  have hnonneg (j : ℕ) :
      0 ≤ inSourceOldEnergyHistoryWeight M j*inSourceMeanActual M m j t :=
    mul_nonneg (parent_gap_weight_nonneg M j)
      (in_source_actual_mean_nonneg M m j t)
  have hsum := Summable.of_nonneg_of_le hnonneg hpoint hmajorant
  have hbound := hsum.tsum_le_tsum hpoint hmajorant
  rw [hendpoint.1.tsum_add (hslope.mul_left t),tsum_mul_left] at hbound
  refine ⟨hsum,?_⟩
  calc
    _ ≤ (∑' j : ℕ,inSourceOldEnergyHistoryWeight M j*(nativeCompletedSourceMean M m j).toReal)+
        t*(∑' j : ℕ,inSourceOldEnergyHistoryWeight M j*inSourceMeanSlopeActual M h m j) := hbound
    _ ≤ mixedBridgeXiPre M+
        t*(∑' j : ℕ,inSourceOldEnergyHistoryWeight M j*inSourceMeanSlopeActual M h m j) :=
      add_le_add (hendpoint.2.trans (parent_gap_root_weak_endpoint M h hM hg N hpast m hm)) le_rfl
    _ = _ := by rw [←mixed_bridge_xi_slope_eq_source_series]

end
end ASDExplicitGamma.Inverse
