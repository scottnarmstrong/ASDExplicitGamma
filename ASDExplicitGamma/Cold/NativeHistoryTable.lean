module

public import ASDExplicitGamma.Cold.NativeHistoryCells
public import ASDExplicitGamma.Cold.NativeFluctuationTable
public import ASDExplicitGamma.Cold.ColdHistoryTable
public import ASDExplicitGamma.Cold.ColdTableGlobalBounds

/-! # The actual complete native history fits the checked history table -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The complete actual native depth history, with all source cells and all fine depths. -/
def coldNativeHistory (M : ABKModel 2) (m : ℤ) (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  coldWeightedHistory coldHistoryAlpha (fun r => coldFiniteMaximum (coldNativeHistoryArray M m j r) ω)

/-- The genuine fixed-native-model history is in L20 and bounded by theta times its checked endpoint.
All prefix cell/fluctuation caps are derived from the actual native moment system; the complete
fine tail is paid by the exact frozen strong20 sum. -/
theorem cold_native_history_table (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    (hstrong : strong20 M m ≤ ENNReal.ofReal (θ*(coldS20:ℝ)))
    {j : ℕ} (hj : j ∈ coldUpdatedLags)
    (hmean : ∀ k < j, coldNativeMean M m k ≤ θ*(coldMeanAt k:ℝ)) :
    MemLp (coldNativeHistory M m j) 20 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (coldNativeHistory M m j) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ θ*(coldHistoryAt j:ℝ) := by
  have hjb := cold_updated_lag_bounds j hj
  let MM := fun k => θ*(coldMomentAt k:ℝ)
  let DD := fun k => θ*(coldMeanAt k:ℝ)
  let root : ℕ → ℝ := fun k => lpNorm (cutoffTraceDefect M m (m-(k:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure
  have hMM (k : ℕ) : 0 ≤ MM k := mul_nonneg hθ (Rat.cast_nonneg.mpr (cold_table_global_bounds k).1)
  have hDD (k : ℕ) : 0 ≤ DD k := mul_nonneg hθ (Rat.cast_nonneg.mpr (cold_table_global_bounds k).2.2)
  have ha : 0 ≤ θ*(coldA:ℝ) := mul_nonneg hθ (by norm_num [coldA])
  have hR : 0 ≤ θ*(coldR20:ℝ) := mul_nonneg hθ (by norm_num [coldR20])
  have hS : 0 ≤ θ*(coldS20:ℝ) := mul_nonneg hθ (by norm_num [coldS20])
  have hraw (r : ℕ) (hr : r < j) (i : Fin (9^r)) :
      lpNorm (coldNativeHistoryArray M m j r i) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ MM (j-r) := by
    have he := congrArg ENNReal.toReal ((coldNativeHistoryArray_prefix_sameLaw M m j r hr.le i).eLpNorm_eq (p := 20))
    exact he.trans_le (cold_native_moment_table M h hM m hθ hroot (by omega)
      (fun k hk => hmean k (by omega)))
  have hfluct (r : ℕ) (hr : r < j) (k : ℕ) (hk : k ∈ coldHistoryEarlierLags j r) (i : Fin (9^r)) :
      lpNorm (fun ω => max (coldNativeHistoryArray M m j r i ω-DD k) 0) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        coldCenteredMomentCap (MM k) (j-r-k) := by
    have hklt := coldHistoryEarlierLags_lt (by omega : 0 < j) hk
    have hkle : k ≤ j-r := by
      have hh : k < min (j-r) (j-1)+1 := Finset.mem_range.mp hk
      omega
    have he := (coldNativeHistoryArray_prefix_sameLaw M m j r hr.le i).comp (u := fun x : ℝ => max (x-DD k) 0)
      (measurable_id.sub_const (DD k) |>.max measurable_const)
    have hn := congrArg ENNReal.toReal (he.eLpNorm_eq (p := 20))
    exact hn.trans_le (cold_native_fluctuation_table M h hM m hθ hroot hjb.2 hklt hkle hmean)
  have hfar (k : ℕ) (i : Fin (9^(k+j))) :
      lpNorm (coldNativeHistoryArray M m j (k+j) i) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ root k := by
    exact (congrArg ENNReal.toReal ((coldNativeHistoryArray_fine_sameLaw M m j k i).eLpNorm_eq (p := 20))).le
  have hStrong := cold_native_strong_sum hS hstrong
  have hglobal : (1-coldHistoryAlpha)*(θ*(coldR20:ℝ)) ≤ (1-coldHistoryBeta)*(θ*(coldS20:ℝ)) := by
    have heR : θ*(coldR20:ℝ) = (2013/10000:ℝ)*θ := by
      norm_num only [coldR20,Rat.cast_div,Rat.cast_ofNat]
      ring
    have heS : θ*(coldS20:ℝ) = (2379/2500:ℝ)*θ := by
      norm_num only [coldS20,Rat.cast_div,Rat.cast_ofNat]
      ring
    rw [heR,heS]
    exact cold_history_native_constants hθ
  have hM0 : MM 0 = θ*(coldR20:ℝ) := by dsimp only [MM]; rw [cold_table_zero.2]
  have hD0 : DD 0 ≤ θ*(coldA:ℝ) := by dsimp only [DD]; rw [cold_table_zero.1]
  have hMR (k : ℕ) : MM k ≤ θ*(coldR20:ℝ) :=
    mul_le_mul_of_nonneg_left (Rat.cast_le.mpr (cold_table_global_bounds k).2.1) hθ
  have hcap := cold_history_caps (coldNativeHistoryArray M m j) ha hR hMM hDD hM0 hD0 hMR hglobal
    (coldNativeHistoryArray_memLp hroot hstrong j)
    (fun r i => coldNativeCellTrace_measurable M m (coldNativeHistoryCell m j r i))
    (fun r i => Filter.Eventually.of_forall (coldNativeCellTrace_nonneg M m (coldNativeHistoryCell m j r i)))
    hraw hfluct hfar hStrong.1 hStrong.2
  refine ⟨hcap.1,hcap.2.trans ?_⟩
  exact cold_history_table_scaled hθ hj

end ASDExplicitGamma.Cold
