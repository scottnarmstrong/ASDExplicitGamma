module

public import ASDExplicitGamma.Inverse.SourceInterfaceEnergy
public import ASDExplicitGamma.Inverse.SourceInterfaceHistory
public import ASDExplicitGamma.Inverse.SourceTransport

/-! IN-SOURCE-ENERGY instantiated on the actual OLD law and true frame. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Algsuperdiff.Section3
open ASDExplicitGamma.Native
open scoped ENNReal

private theorem in_source_old_energy_history_weight_nonneg
    (M : ABKModel 2) (r : ℕ) :
    0 ≤ inSourceOldEnergyHistoryWeight M r := by
  have hα := Scalar.inverse_history_discount_range
  have hpref : 0 ≤ 1 - Scalar.inverseHistoryDiscount ^ 2 := by
    nlinarith [hα.1, hα.2]
  unfold inSourceOldEnergyHistoryWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply mul_nonneg hpref
      exact pow_nonneg hα.1.le _
    · norm_num
  · exact Real.rpow_nonneg (by norm_num) _

/-- The OLD source slopes, finite and complete weighted energy bounds, and
common-center transport on the actual completed law. The finite transport
uses the preceding transport theorem; the complete passage uses the
summability and monotone-history interface. -/
theorem in_source_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) :
    (∀ r : ℕ,
      0 ≤ inSourceMeanSlopeActual M h m r ∧
        inSourceMeanSlopeActual M h m r ≤ inSourceOldEnergyCap M h m r) ∧
    (∀ K : ℕ,
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) ≤
      ∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r) ∧
    (Summable (fun r : ℕ =>
        inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) ∧
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        inSourceMeanSlopeActual M h m r) ≤
      ∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
        inSourceOldEnergyCap M h m r) ∧
    (∀ K : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t) ≤
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r *
          (nativeCompletedSourceMean M m r).toReal) +
        t * (∑ r ∈ Finset.range K,
          inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Summable (fun r : ℕ =>
        inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t) ∧
      (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t) ≤
        (∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
          (nativeCompletedSourceMean M m r).toReal) +
          t * (∑' r : ℕ,
            inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r)) := by
  have hSmall : NativeSourceSmallerGammaBounds M m :=
    native_source_smaller_gamma M h hM hg N hpast m hm
  have hpastM : ∀ k < m, nativeInductionState M h k :=
    fun k hk => hpast k (hk.trans hm)
  have hTransport := in_source_transport M h hM hg N hpast m hm
  have hCompleteEnergy :=
    in_source_actual_complete_old_energy_sum M h hM hg m hpastM
  have hFiniteTransport : ∀ K : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t) ≤
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r *
          (nativeCompletedSourceMean M m r).toReal) +
        t * (∑ r ∈ Finset.range K,
          inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) := by
    intro K t ht
    calc
      _ ≤ ∑ r ∈ Finset.range K,
          inSourceOldEnergyHistoryWeight M r *
            (inSourceMeanActual M m r 0 + t * inSourceMeanSlopeActual M h m r) := by
          apply Finset.sum_le_sum
          intro r hr
          exact mul_le_mul_of_nonneg_left (hTransport.1 r t ht)
            (in_source_old_energy_history_weight_nonneg M r)
      _ = (∑ r ∈ Finset.range K,
            inSourceOldEnergyHistoryWeight M r *
              (nativeCompletedSourceMean M m r).toReal) +
          t * (∑ r ∈ Finset.range K,
            inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) := by
          calc
            _ = ∑ r ∈ Finset.range K,
                (inSourceOldEnergyHistoryWeight M r *
                    (nativeCompletedSourceMean M m r).toReal +
                  t * (inSourceOldEnergyHistoryWeight M r *
                    inSourceMeanSlopeActual M h m r)) := by
                apply Finset.sum_congr rfl
                intro r hr
                rw [hTransport.2.1 r]
                ring
            _ = _ := by
                rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hFiniteCommon : ∀ K : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r * inSourceMeanActual M m r t) ≤
      (∑ r ∈ Finset.range K,
        inSourceOldEnergyHistoryWeight M r *
          (nativeCompletedSourceMean M m r).toReal) +
        t * (∑ r ∈ Finset.range K,
          inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r) := by
    intro K t ht
    have hFiniteEnergy :=
      in_source_actual_finite_old_energy_sum M h hM hg m hpastM K
    calc
      _ ≤ (∑ r ∈ Finset.range K,
            inSourceOldEnergyHistoryWeight M r *
              (nativeCompletedSourceMean M m r).toReal) +
          t * (∑ r ∈ Finset.range K,
            inSourceOldEnergyHistoryWeight M r * inSourceMeanSlopeActual M h m r) :=
        hFiniteTransport K t ht
      _ ≤ (∑ r ∈ Finset.range K,
            inSourceOldEnergyHistoryWeight M r *
              (nativeCompletedSourceMean M m r).toReal) +
          t * (∑ r ∈ Finset.range K,
            inSourceOldEnergyHistoryWeight M r * inSourceOldEnergyCap M h m r) :=
        by
          have hScaled := mul_le_mul_of_nonneg_left hFiniteEnergy ht.1
          linarith
  refine ⟨?_, ?_, hCompleteEnergy, hFiniteCommon, ?_⟩
  · intro r
    constructor
    · change 0 ≤ max 0 (sSup
        (inSourceMeanRateActual M h m r '' Set.Icc (0 : ℝ) 1))
      exact le_max_left _ _
    · exact in_source_actual_slope_old_energy_bound M h hM hg m hpastM r
  · intro K
    exact in_source_actual_finite_old_energy_sum M h hM hg m hpastM K
  · intro t ht
    exact in_source_actual_complete_common_center_transport_by_caps
      M h hM hg m hpastM hSmall t ht

end ASDExplicitGamma.Inverse
