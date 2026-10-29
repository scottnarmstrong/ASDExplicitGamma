module

public import ASDExplicitGamma.Cold.ColdGraphOldTable

/-! # Analytic consumption of the chosen graph certificate -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The exact real source candidate selected by the certified finite choice table.
Any minimum over all available candidates is no larger than this candidate. -/
def coldSelectedGraphCap (θ : ℝ) (ell : ℕ) : ℝ :=
  let choice := coldGraphChoiceAt ell
  if choice = 0 then coldOldGraphCap (θ*(coldA:ℝ)) (θ*(coldL0:ℝ)) ell
  else if choice % 2 = 1 then
    let k := (choice-1)/2
    coldFiveSixthsGraphCap (θ*(coldMeanAt k:ℝ)) (θ*(coldInterpolationAt k:ℝ)) (ell-k)
  else
    let k := (choice-2)/2
    coldSandwichGraphCap (θ*(coldMeanAt k:ℝ)) (θ*(coldInterpolationAt k:ℝ)) (ell-k)

/-- Every chosen endpoint source graph candidate fits its producing rational table entry. -/
theorem cold_selected_graph_table {ell : ℕ} (hell : ell ≤ 126) :
    coldSelectedGraphCap 1 ell ≤ (coldGraphAt ell:ℝ) := by
  have hmem : ell ∈ coldCheckedGraphLags := List.mem_range.mpr (by omega)
  have hk := cold_graph_choice_lag ell hmem
  have hout := cold_round_up_real (coldGraphChoiceValue ell)
  rw [cold_graph_table_check ell hmem]
  apply LE.le.trans (b := (coldGraphChoiceValue ell:ℝ)) ?_ hout
  unfold coldSelectedGraphCap coldGraphChoiceValue
  dsimp only
  split_ifs with hzero hodd
  · simpa only [one_mul] using cold_old_graph_table ell
  · simpa only [one_mul] using cold_five_sixths_graph_table hell (hk.1.trans hell) hzero hodd rfl
  · simpa only [one_mul] using cold_sandwich_graph_table hell (hk.2.trans hell) hzero hodd rfl

/-- The selected analytic graph cap scales by at most theta, without changing the choice. -/
theorem cold_selected_graph_scale {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {ell : ℕ} (hell : ell ≤ 126) :
    coldSelectedGraphCap θ ell ≤ θ*coldSelectedGraphCap 1 ell := by
  have hmem : ell ∈ List.range 127 := List.mem_range.mpr (by omega)
  have hk := cold_graph_choice_lag ell hmem
  unfold coldSelectedGraphCap
  dsimp only
  split_ifs
  · simpa only [one_mul] using coldOldGraphCap_scale hθ hθ1
      (show 0 ≤ (coldA:ℝ) by norm_num [coldA]) (show 0 ≤ (coldL0:ℝ) by norm_num [coldL0]) ell
  · simpa only [one_mul] using coldFiveSixthsGraphCap_scale hθ hθ1
      (D := (coldMeanAt ((coldGraphChoiceAt ell-1)/2):ℝ))
      (L := (coldInterpolationAt ((coldGraphChoiceAt ell-1)/2):ℝ)) (ell-(coldGraphChoiceAt ell-1)/2)
  · have hD : 0 ≤ (coldMeanAt ((coldGraphChoiceAt ell-2)/2):ℝ) := Rat.cast_nonneg.mpr
      (cold_table_nonneg _ (List.mem_range.mpr (by omega))).1
    simpa only [one_mul] using coldSandwichGraphCap_scale hθ hθ1 hD
      (L := (coldInterpolationAt ((coldGraphChoiceAt ell-2)/2):ℝ)) (ell-(coldGraphChoiceAt ell-2)/2)

/-- Proportionally scaled exact source graph caps fit theta times the endpoint table. -/
theorem cold_selected_graph_table_scaled {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {ell : ℕ} (hell : ell ≤ 126) :
    coldSelectedGraphCap θ ell ≤ θ*(coldGraphAt ell:ℝ) :=
  (cold_selected_graph_scale hθ hθ1 hell).trans
    (mul_le_mul_of_nonneg_left (cold_selected_graph_table hell) hθ)

end ASDExplicitGamma.Cold
