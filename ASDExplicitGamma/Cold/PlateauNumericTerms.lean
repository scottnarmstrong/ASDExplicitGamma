module

public import ASDExplicitGamma.Cold.PlateauNumerics
public import ASDExplicitGamma.Cold.ColdHistoryTable

/-! # Producing constants and source terms for the checked cold recurrence -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- All frozen plateau parameters and thresholds have their source signs. -/
theorem cold_plateau_parameters : ∀ j ∈ coldUpdatedLags,
    0 < (paramsForLag j).c ∧ (paramsForLag j).c < 1 ∧ 0 < (paramsForLag j).t ∧
      0 < (paramsForLag j).eta ∧ 0 < coldXi j ∧ 0 ≤ coldHistoryAt j := by
  decide +kernel

/-- Literal conversion of the four producing plateau constants to the real field. -/
theorem plateau_constants_numeric (j : ℕ) :
    (coldCT j:ℝ) = 4/(7*(1-((paramsForLag j).c:ℝ))) ∧
    (coldCD j:ℝ) = 96/(49*((paramsForLag j).c:ℝ))-1 ∧
    (coldG0 j:ℝ) = 2*(1+((paramsForLag j).eta:ℝ)) ∧
    (coldG1 j:ℝ) = 2+1/(4*((paramsForLag j).eta:ℝ)) := by
  unfold coldCT coldCD coldG0 coldG1
  push_cast
  rw [div_div]
  exact ⟨rfl,rfl,rfl,rfl⟩

/-- Literal conversion of the graph source term to the finite even-depth sum. -/
theorem plateau_graph_term_numeric (J : ℕ) :
    (coldCT (2*J):ℝ)*(1+((paramsForLag (2*J)).t:ℝ))*
      (∑ k ∈ Finset.range J, plateauEvenWeight k*(coldGraphAt (2*J-2*(k+1)):ℝ)) =
        (coldGraphContribution (2*J):ℝ) := by
  unfold coldGraphContribution
  rw [Rat.cast_mul,Rat.cast_mul,Rat.cast_add,Rat.cast_one,← coldRealListSum_cast]
  change _ = (coldCT (2*J):ℝ)*(1+((paramsForLag (2*J)).t:ℝ))*
    coldRealListSum (coldTransportIndices (2*J)) (fun r => ((coldWeight r*coldGraphAt (2*J-r):ℚ):ℝ))
  rw [plateau_transport_sum_numeric]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [plateau_weight_numeric,Rat.cast_mul]

/-- Literal conversion of the one-time source bad charge. -/
theorem plateau_bad_term_numeric (j : ℕ) :
    (55/4:ℝ)*(coldCT j:ℝ)*(coldG1 j:ℝ)*(1+1/((paramsForLag j).t:ℝ))*
      (coldHistoryAt j:ℝ)^20/(coldXi j:ℝ)^18 = (coldBadHistory j:ℝ) := by
  unfold coldBadHistory
  push_cast
  rfl

/-- The exact weighted source means are the replay's real weighted means. -/
theorem plateau_mean_term_numeric (μ : ℕ → ℝ) (J : ℕ) :
    (∑ k ∈ Finset.range J,
      plateauLagCoefficient (coldCT (2*J):ℝ) (coldCD (2*J):ℝ)
        (1+1/((paramsForLag (2*J)).t:ℝ)) (coldG0 (2*J):ℝ) (coldG1 (2*J):ℝ) (coldXi (2*J):ℝ) k*
          μ (2*J-2*(k+1))) = coldExactWeightedMeans μ (2*J) := by
  simp_rw [plateau_lag_numeric]
  exact (plateau_transport_sum_numeric J (fun r => coldExactQ (2*J) r*μ (2*J-r))).symm

end ASDExplicitGamma.Cold
