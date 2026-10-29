module

public import ASDExplicitGamma.Native.HeatInitialNumericsEFactorGen

/-! Assembly of the numeric certificates `NativeHeatGenNum ns` from the generated
per-shell-count data (`nativeHeatNNNVariance`, `…Spectral`, `…Qm` and their `_formula`
theorems). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The initial mean moments of orders `0, …, 20`, tabulated once. -/
def nativeHeatGenMMTab : List ℚ :=
  (List.range 21).map (nativeInitialMeanMoment nativeHeatParametersData)

theorem nativeHeatGenMMTab_getD (n : ℕ) (hn : n ≤ 20) :
    nativeHeatGenMMTab.getD n 0 =
      nativeInitialMeanMoment nativeHeatParametersData n := by
  unfold nativeHeatGenMMTab
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, show n < 21 by omega]

/-- Computed base-row root certificates for a moment list (tabulated mean moments). -/
def nativeHeatGenBaseOk (qm : List ℚ) : Bool :=
  (List.range' 2 19).all fun k =>
    nativeRootValid
      (nativeUp (((List.range (k + 1)).map fun j =>
        (Nat.choose k j : ℚ) * nativeHeatGenMMTab.getD (k - j) 0 *
          (2 * nativeHeatB) ^ j * qm.getD j 0).sum)) k

/-- Computed outward root certificates for a moment list. -/
def nativeHeatGenRootOk (qm : List ℚ) : Bool :=
  (List.range' 1 10).all fun q =>
    nativeRootValid (qm.getD q 0) q &&
      nativeRootValid (nativeRootUp (qm.getD q 0) q) 2

theorem nativeHeatGenNum_of_data (ns : ℕ) (hns : ns ≤ 160) (old : NativeOldRow)
    (hold : nativeHeatOldRowGen ns = old) (V S : ℚ) (Qm : List ℚ)
    (hv : nativeHeatVariance ns old = (V, S))
    (hq : nativeGaussianMoments V S = Qm)
    (hE : nativeHeatGenEUpper ns ≤ old.e)
    (hV0 : 0 ≤ V) (hS0 : 0 ≤ S)
    (hq0 : ∀ j : ℕ, j ≤ 20 → 0 ≤ Qm.getD j 0)
    (hbase : nativeHeatGenBaseOk Qm = true)
    (hroot : nativeHeatGenRootOk Qm = true) :
    NativeHeatGenNum ns := by
  have hVe : nativeHeatGenVariance ns = V := by
    unfold nativeHeatGenVariance
    rw [hold, hv]
  have hSe : nativeHeatGenSpectral ns = S := by
    unfold nativeHeatGenSpectral
    rw [hold, hv]
  have hQe : nativeHeatGenQm ns = Qm := by
    rw [nativeHeatGenQm_eq, hVe, hSe, hq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := nativeHeat_efactor_of_check ns hns (by rw [hold]; exact hE)
    exact this
  · rw [hVe]; exact hV0
  · rw [hSe]; exact hS0
  · rw [hQe]; exact hq0
  · rw [hQe]
    intro k hk2 hk20
    unfold nativeHeatGenBaseOk at hbase
    have hk := List.all_eq_true.mp hbase k (List.mem_range'_1.mpr ⟨hk2, by omega⟩)
    have hsum : ((List.range (k + 1)).map fun j =>
          (Nat.choose k j : ℚ) * nativeHeatGenMMTab.getD (k - j) 0 *
            (2 * nativeHeatB) ^ j * Qm.getD j 0) =
        (List.range (k + 1)).map fun j =>
          (Nat.choose k j : ℚ) *
            nativeInitialMeanMoment nativeHeatParametersData (k - j) *
            (2 * nativeHeatB) ^ j * Qm.getD j 0 := by
      apply List.map_congr_left
      intro j hj
      rw [nativeHeatGenMMTab_getD _ (by have := List.mem_range.mp hj; omega)]
    rw [hsum] at hk
    exact hk
  · rw [hQe]
    intro q hq1 hq10
    unfold nativeHeatGenRootOk at hroot
    have := List.all_eq_true.mp hroot q (List.mem_range'_1.mpr ⟨hq1, by omega⟩)
    exact (Bool.and_eq_true_iff.mp this).1
  · rw [hQe]
    intro q hq1 hq10
    unfold nativeHeatGenRootOk at hroot
    have := List.all_eq_true.mp hroot q (List.mem_range'_1.mpr ⟨hq1, by omega⟩)
    exact (Bool.and_eq_true_iff.mp this).2

end ASDExplicitGamma.Native
