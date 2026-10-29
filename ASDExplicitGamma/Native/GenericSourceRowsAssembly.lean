module

public import ASDExplicitGamma.Native.GenericSourceWeightedRows

/-! Assemble the exact finite generic source profiles into their six weighted
rows, retaining the explicit complete-tail allocation. -/
@[expose] public section

namespace ASDExplicitGamma.Native

/-- The fixed polynomial-geometric tail factor. -/
noncomputable def nativeSourceGenericTailFactor (N : ℕ) : ℝ :=
  ((N + 2 : ℕ) : ℝ) ^ 4 * (9 / 10 : ℝ) ^ (N + 1) *
    (((Nat.factorial 4 : ℕ) : ℝ) * 10 ^ 5)

/-- The retained tail charge based at the initial raw frame for offset `r`. -/
noncomputable def nativeSourceGenericTailCharge
    (gamma theta : ℝ) (r N : ℕ) : ℝ :=
  nativeSourceGenericRawFrame gamma theta (9 + r) *
    nativeSourceGenericTailFactor N

/-- The completed weighted mean row, including its entire explicit tail
charge. -/
noncomputable def nativeSourceGenericCompleteMeanRow
    (gamma theta : ℝ) (r N : ℕ) : ℝ :=
  nativeSourceCompleteWeightedRow (nativeSourceHistoryWeight gamma)
    (fun j => nativeSourceGenericMeanProfile gamma theta (9 + r + j))
    (nativeSourceGenericTailCharge gamma theta r N) N

/-- The completed weighted weak-inverse row, including the same complete
raw-tail allocation. -/
noncomputable def nativeSourceGenericCompleteWeakRow
    (gamma theta : ℝ) (r N : ℕ) : ℝ :=
  nativeSourceCompleteWeightedRow (nativeSourceHistoryWeight gamma)
    (fun j => nativeSourceGenericWeakFrameProfile gamma theta (9 + r + j))
    (nativeSourceGenericTailCharge gamma theta r N) N

/-- A finite weighted source prefix plus the explicit raw-tail charge scales
with degree one when each finite profile and the initial raw frame do. -/
theorem native_source_generic_complete_profile_row_degree
    (gamma theta : ℝ) (r N : ℕ)
    (profile profile0 : ℕ → ℝ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hr : r ≤ 5)
    (hprofile : ∀ j ≤ N, 0 ≤ profile j)
    (hdegree : ∀ j ≤ N, profile j ≤ theta * profile0 j) :
    nativeSourceCompleteWeightedRow (nativeSourceHistoryWeight gamma)
        profile (nativeSourceGenericTailCharge gamma theta r N) N ≤
      theta * nativeSourceCompleteWeightedRow
        (nativeSourceHistoryWeight (17 / 50000)) profile0
          (nativeSourceGenericTailCharge (17 / 50000) 1 r N) N := by
  have hweight := native_source_history_weight_endpoint_and_ratio
    gamma hgamma hgamma0
  have hweight0 := native_source_history_weight_endpoint_and_ratio
    (17 / 50000) (by norm_num) (by norm_num)
  have hheight : 9 + r ≤ 1332 := by omega
  have htailFrame := native_source_generic_raw_frame_degree
    gamma theta (9 + r) hgamma hgamma0 hthetaEq hheight
  have htailFactor : 0 ≤ nativeSourceGenericTailFactor N := by
    unfold nativeSourceGenericTailFactor
    positivity
  have htail : nativeSourceGenericTailCharge gamma theta r N ≤
      theta * nativeSourceGenericTailCharge (17 / 50000) 1 r N := by
    unfold nativeSourceGenericTailCharge
    calc
      _ ≤ theta * nativeSourceGenericRawFrame (17 / 50000) 1 (9 + r) *
          nativeSourceGenericTailFactor N :=
        mul_le_mul_of_nonneg_right htailFrame htailFactor
      _ = theta * nativeSourceGenericTailCharge (17 / 50000) 1 r N := by
        unfold nativeSourceGenericTailCharge
        ring
  exact native_source_complete_weighted_row_degree
    (nativeSourceHistoryWeight gamma)
    (nativeSourceHistoryWeight (17 / 50000)) theta
    (nativeSourceGenericTailCharge gamma theta r N)
    (nativeSourceGenericTailCharge (17 / 50000) 1 r N)
    profile profile0 N hweight.1 hweight0.1 hweight.2.1
    hprofile hdegree htail

/-- Degree-one comparison of the six finite-prefix completed generic mean
rows, including the tail charge. -/
theorem native_source_generic_complete_mean_row_degree
    (gamma theta : ℝ) (r N : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hr : r ≤ 5) (hN : N ≤ 1285) :
    nativeSourceGenericCompleteMeanRow gamma theta r N ≤
      theta * nativeSourceGenericCompleteMeanRow (17 / 50000) 1 r N := by
  have hprofile : ∀ j ≤ N,
      0 ≤ nativeSourceGenericMeanProfile gamma theta (9 + r + j) := by
    intro j hj
    exact native_source_generic_mean_profile_nonneg gamma theta (9 + r + j)
      hgamma (by rw [hthetaEq]; positivity) hgamma0 (by omega)
  have hdegree : ∀ j ≤ N,
      nativeSourceGenericMeanProfile gamma theta (9 + r + j) ≤
        theta * nativeSourceGenericMeanProfile (17 / 50000) 1 (9 + r + j) := by
    intro j hj
    exact native_source_generic_mean_profile_degree gamma theta (9 + r + j)
      hgamma hgamma0 hthetaEq (by omega)
  unfold nativeSourceGenericCompleteMeanRow
  exact native_source_generic_complete_profile_row_degree gamma theta r N
    (fun j => nativeSourceGenericMeanProfile gamma theta (9 + r + j))
    (fun j => nativeSourceGenericMeanProfile (17 / 50000) 1 (9 + r + j))
    hgamma hgamma0 hthetaEq hr hprofile hdegree

/-- Degree-one comparison of the six finite-prefix completed weak-inverse
rows, including the tail charge. -/
theorem native_source_generic_complete_weak_row_degree
    (gamma theta : ℝ) (r N : ℕ)
    (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000)
    (hthetaEq : theta = gamma / (17 / 50000 : ℝ))
    (hr : r ≤ 5) (hN : N ≤ 1285) :
    nativeSourceGenericCompleteWeakRow gamma theta r N ≤
      theta * nativeSourceGenericCompleteWeakRow (17 / 50000) 1 r N := by
  have hprofile : ∀ j ≤ N,
      0 ≤ nativeSourceGenericWeakFrameProfile gamma theta (9 + r + j) := by
    intro j hj
    exact native_source_generic_weak_frame_profile_nonneg gamma theta (9 + r + j)
      hgamma (by rw [hthetaEq]; positivity) hgamma0 (by omega)
  have hdegree : ∀ j ≤ N,
      nativeSourceGenericWeakFrameProfile gamma theta (9 + r + j) ≤
        theta * nativeSourceGenericWeakFrameProfile (17 / 50000) 1 (9 + r + j) := by
    intro j hj
    exact native_source_generic_weak_frame_profile_degree gamma theta (9 + r + j)
      hgamma hgamma0 hthetaEq (by omega)
  unfold nativeSourceGenericCompleteWeakRow
  exact native_source_generic_complete_profile_row_degree gamma theta r N
    (fun j => nativeSourceGenericWeakFrameProfile gamma theta (9 + r + j))
    (fun j => nativeSourceGenericWeakFrameProfile (17 / 50000) 1 (9 + r + j))
    hgamma hgamma0 hthetaEq hr hprofile hdegree

end ASDExplicitGamma.Native
