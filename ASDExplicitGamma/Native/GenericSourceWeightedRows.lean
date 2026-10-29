module

public import ASDExplicitGamma.Native.GenericSourceTail
public import ASDExplicitGamma.Native.GenericSourceFullResponse
public import ASDExplicitGamma.Numerics.Inverse.RealBounds

/-! The finite weighted rows and their retained complete tails.
The producer profiles remain explicit parameters here, so the analytic source
transport and endpoint certificate can be instantiated without being hidden in
an altered theorem premise. -/
@[expose] public section

namespace ASDExplicitGamma.Native

/-- Lower endpoint for the positive history weight. -/
noncomputable def nativeSourceAlphaMinus : ℝ := 759835 / 1000000

/-- Upper endpoint for the positive history weight. -/
noncomputable def nativeSourceAlphaPlus : ℝ := 759836 / 1000000

/-- The full geometric row weight `q_γ = α₊² E(2γ)`. -/
noncomputable def nativeSourceHistoryWeight (gamma : ℝ) : ℝ :=
  nativeSourceAlphaPlus ^ 2 * nativeSourceE gamma 1

/-- The finite weighted source sum, with all indices `j≤N`. -/
noncomputable def nativeSourceFiniteWeightedRow
    (q : ℝ) (profile : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), q ^ j * profile j

/-- The complete weighted source row: its finite prefix plus its explicit
entire tail charge. -/
noncomputable def nativeSourceCompleteWeightedRow
    (q : ℝ) (profile : ℕ → ℝ) (tail : ℝ) (N : ℕ) : ℝ :=
  nativeSourceFiniteWeightedRow q profile N + tail

/-- The history weights are nonnegative, endpoint-dominated, and pass the
retained ratio gate against the true exponential growth `3^(6γ)`. -/
theorem native_source_history_weight_endpoint_and_ratio
    (gamma : ℝ) (hgamma : 0 ≤ gamma) (hgamma0 : gamma ≤ 17 / 50000) :
    0 ≤ nativeSourceHistoryWeight gamma ∧
      nativeSourceHistoryWeight gamma ≤ nativeSourceHistoryWeight (17 / 50000) ∧
      nativeSourceHistoryWeight gamma * (3 : ℝ) ^ (6 * gamma) ≤ 9 / 10 := by
  have hE := native_source_E_le_endpoint gamma 1 hgamma hgamma0 (by omega)
  have hEpos := native_source_E_nonneg gamma 1 hgamma hgamma0 (by omega)
  have hE0pos := native_source_E_nonneg (17 / 50000) 1
    (by norm_num) (by norm_num) (by omega)
  have hweightNonneg : 0 ≤ nativeSourceHistoryWeight gamma := by
    unfold nativeSourceHistoryWeight
    exact mul_nonneg (sq_nonneg _) hEpos
  have hweightEndpoint : nativeSourceHistoryWeight gamma ≤
      nativeSourceHistoryWeight (17 / 50000) := by
    unfold nativeSourceHistoryWeight
    exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)
  have hweight0Nonneg : 0 ≤ nativeSourceHistoryWeight (17 / 50000) := by
    unfold nativeSourceHistoryWeight
    exact mul_nonneg (sq_nonneg _) hE0pos
  have hpowOrder : 6 * gamma ≤ 10 * (17 / 50000 : ℝ) := by
    nlinarith [hgamma0]
  have hpow : (3 : ℝ) ^ (6 * gamma) ≤
      (3 : ℝ) ^ (10 * (17 / 50000 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    exact hpowOrder
  have hpowEndpoint : (3 : ℝ) ^ (10 * (17 / 50000 : ℝ)) ≤
      nativeSourceE (17 / 50000) 5 := by
    have h := Numerics.Inverse.inv_three_power_bound
      (10 * (17 / 50000 : ℝ)) (by norm_num) (by norm_num)
    convert h using 1
    norm_num [nativeSourceE]
  have hratioEndpoint :
      nativeSourceHistoryWeight (17 / 50000) * nativeSourceE (17 / 50000) 5 ≤
        9 / 10 := by
    norm_num [nativeSourceHistoryWeight, nativeSourceAlphaPlus, nativeSourceE]
  have hratio : nativeSourceHistoryWeight gamma * (3 : ℝ) ^ (6 * gamma) ≤
      nativeSourceHistoryWeight (17 / 50000) * nativeSourceE (17 / 50000) 5 := by
    calc
      _ ≤ nativeSourceHistoryWeight (17 / 50000) * (3 : ℝ) ^ (6 * gamma) :=
        mul_le_mul_of_nonneg_right hweightEndpoint (by positivity)
      _ ≤ nativeSourceHistoryWeight (17 / 50000) *
          nativeSourceE (17 / 50000) 5 :=
        mul_le_mul_of_nonneg_left (hpow.trans hpowEndpoint) hweight0Nonneg
  exact ⟨hweightNonneg, hweightEndpoint, hratio.trans hratioEndpoint⟩

/-- Degree-one comparison of a finite nonnegative weighted source row. -/
theorem native_source_finite_weighted_row_degree
    (q q0 theta : ℝ) (profile profile0 : ℕ → ℝ) (N : ℕ)
    (hq : 0 ≤ q) (hq0 : 0 ≤ q0) (hqq0 : q ≤ q0)
    (hprofile : ∀ j ≤ N, 0 ≤ profile j)
    (hdegree : ∀ j ≤ N, profile j ≤ theta * profile0 j) :
    nativeSourceFiniteWeightedRow q profile N ≤
      theta * nativeSourceFiniteWeightedRow q0 profile0 N := by
  unfold nativeSourceFiniteWeightedRow
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 1), theta * (q0 ^ j * profile0 j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j ≤ N := by simp only [Finset.mem_range] at hj; omega
      calc
        q ^ j * profile j ≤ q0 ^ j * profile j :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq hqq0 j) (hprofile j hjN)
        _ ≤ q0 ^ j * (theta * profile0 j) :=
          mul_le_mul_of_nonneg_left (hdegree j hjN) (pow_nonneg hq0 j)
        _ = theta * (q0 ^ j * profile0 j) := by ring
    _ = theta * nativeSourceFiniteWeightedRow q0 profile0 N := by
      rw [nativeSourceFiniteWeightedRow, ← Finset.mul_sum]

/-- Degree-one comparison of a complete weighted row, with the explicit
tail kept as a summand. -/
theorem native_source_complete_weighted_row_degree
    (q q0 theta tail tail0 : ℝ) (profile profile0 : ℕ → ℝ) (N : ℕ)
    (hq : 0 ≤ q) (hq0 : 0 ≤ q0) (hqq0 : q ≤ q0)
    (hprofile : ∀ j ≤ N, 0 ≤ profile j)
    (hdegree : ∀ j ≤ N, profile j ≤ theta * profile0 j)
    (htail : tail ≤ theta * tail0) :
    nativeSourceCompleteWeightedRow q profile tail N ≤
      theta * nativeSourceCompleteWeightedRow q0 profile0 tail0 N := by
  unfold nativeSourceCompleteWeightedRow
  calc
    _ ≤ theta * nativeSourceFiniteWeightedRow q0 profile0 N + theta * tail0 :=
      add_le_add
        (native_source_finite_weighted_row_degree q q0 theta profile profile0 N
          hq hq0 hqq0 hprofile hdegree)
        htail
    _ = theta * nativeSourceCompleteWeightedRow q0 profile0 tail0 N := by
      unfold nativeSourceCompleteWeightedRow
      ring

/-- The weak-inverse row conversion, retaining both the OLD
order-128 cap and its `ε`-weighted companion row. -/
noncomputable def nativeSourceWeakInverseCharge (W V : ℝ) : ℝ :=
  (1 - nativeSourceAlphaMinus ^ 2) *
    (nativeSourceB128 * W + (3 / 10 ^ 46 : ℝ) * V)

/-- Degree-one comparison of the exact weak-inverse charge. -/
theorem native_source_weak_inverse_charge_degree
    (theta W W0 V V0 : ℝ)
    (hW : W ≤ theta * W0) (hV : V ≤ theta * V0) :
    nativeSourceWeakInverseCharge W V ≤ theta *
      nativeSourceWeakInverseCharge W0 V0 := by
  have hb : 0 ≤ nativeSourceB128 := by norm_num [nativeSourceB128]
  have heps : 0 ≤ (3 / 10 ^ 46 : ℝ) := by norm_num
  have hw : 0 ≤ 1 - nativeSourceAlphaMinus ^ 2 := by
    norm_num [nativeSourceAlphaMinus]
  have hsum : nativeSourceB128 * W + (3 / 10 ^ 46 : ℝ) * V ≤
      theta * (nativeSourceB128 * W0 + (3 / 10 ^ 46 : ℝ) * V0) := by
    have hfirst : nativeSourceB128 * W ≤
        theta * (nativeSourceB128 * W0) := by
      calc
        nativeSourceB128 * W ≤ nativeSourceB128 * (theta * W0) :=
          mul_le_mul_of_nonneg_left hW hb
        _ = theta * (nativeSourceB128 * W0) := by ring
    have hsecond : (3 / 10 ^ 46 : ℝ) * V ≤
        theta * ((3 / 10 ^ 46 : ℝ) * V0) := by
      calc
        (3 / 10 ^ 46 : ℝ) * V ≤ (3 / 10 ^ 46 : ℝ) * (theta * V0) :=
          mul_le_mul_of_nonneg_left hV heps
        _ = theta * ((3 / 10 ^ 46 : ℝ) * V0) := by ring
    calc
      _ ≤ theta * (nativeSourceB128 * W0) +
          theta * ((3 / 10 ^ 46 : ℝ) * V0) :=
        add_le_add hfirst hsecond
      _ = _ := by ring
  unfold nativeSourceWeakInverseCharge
  calc
    _ ≤ (1 - nativeSourceAlphaMinus ^ 2) *
        (theta * (nativeSourceB128 * W0 + (3 / 10 ^ 46 : ℝ) * V0)) :=
      mul_le_mul_of_nonneg_left hsum hw
    _ = theta * nativeSourceWeakInverseCharge W0 V0 := by
      simp [nativeSourceWeakInverseCharge]
      ring

end ASDExplicitGamma.Native
