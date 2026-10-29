module

public import ASDExplicitGamma.Cold.PlateauRecurrenceCoefficients
public import ASDExplicitGamma.Cold.ColdMeanInduction
public import ASDExplicitGamma.Cold.ColdOutwardSum

/-! # Identification of the analytic plateau coefficients with the checked recurrence -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Exact agreement of the source even weights, including the exceptional depth two. -/
theorem plateau_weight_numeric (k : ℕ) : plateauEvenWeight k = (coldWeight (2*(k+1)):ℝ) := by
  have hd : 2*(k+1)/2 = k+1 := by omega
  by_cases hk : k = 0
  · subst k
    norm_num [plateauEvenWeight,coldWeight]
  · have hk2 : 2*(k+1) ≠ 2 := by omega
    rw [plateauEvenWeight,ite_eq_right hk,coldWeight,ite_eq_right hk2,hd]
    push_cast
    rw [div_pow,one_pow]
    ring

/-- The actual even-depth coefficient is the exact sqrt(3) coefficient of the replay. -/
theorem plateau_lag_numeric (j k : ℕ) :
    plateauLagCoefficient (coldCT j:ℝ) (coldCD j:ℝ) (1+1/((paramsForLag j).t:ℝ))
      (coldG0 j:ℝ) (coldG1 j:ℝ) (coldXi j:ℝ) k = coldExactQ j (2*(k+1)) := by
  have hd : 2*(k+1)/2 = k+1 := by omega
  have hk4 : 2*(k+1) = 4 ↔ k = 1 := by omega
  unfold plateauLagCoefficient plateauGramWeight coldExactQ coldQAtRoot coldQRootBase coldQRootCoeff
  rw [plateau_weight_numeric,hd]
  push_cast
  simp only [hk4]
  split_ifs <;> ring

/-- Split the exact infinite Gram tail into its two source geometric series. -/
theorem plateau_gram_tail {J : ℕ} (hJ : 1 ≤ J) (g0 g1 ξ : ℝ) :
    (∑' k : ℕ, plateauGramWeight g0 g1 ξ (k+J)) =
      g0*((7/2:ℝ)*(1/9:ℝ)^J)+
        g1*ξ*(28*(Real.sqrt 3/9)^(J+1)/(1-Real.sqrt 3/9)) := by
  have hw : Summable (fun k : ℕ => plateauEvenWeight (k+J)) :=
    (summable_nat_add_iff J).mpr summable_plateauEvenWeight
  have hs : Summable (fun k : ℕ => plateauEvenWeight (k+J)*(Real.sqrt 3)^(k+J+1)) :=
    (summable_nat_add_iff J).mpr summable_plateauEvenWeight_sqrtThree
  have he (k : ℕ) : plateauGramWeight g0 g1 ξ (k+J) =
      g0*plateauEvenWeight (k+J)+(g1*ξ)*(plateauEvenWeight (k+J)*(Real.sqrt 3)^(k+J+1)) := by
    unfold plateauGramWeight
    ring
  simp_rw [he]
  rw [(hw.mul_left _).tsum_add (hs.mul_left _),tsum_mul_left,tsum_mul_left,
    plateau_tail hJ,plateau_sqrtThree_tail hJ]

/-- The exact fine coefficient agrees with the closed sqrt(3) tail of the replay. -/
theorem plateau_fine_numeric {J : ℕ} (hJ : 1 ≤ J) :
    plateauFineCoefficient (coldCT (2*J):ℝ) (coldG0 (2*J):ℝ) (coldG1 (2*J):ℝ)
      (coldXi (2*J):ℝ) J = coldExactFine (2*J) := by
  have hd : 2*J/2 = J := by omega
  have he : (1/3:ℝ)^(2*J) = (1/9:ℝ)^J := by
    rw [pow_mul]
    norm_num
  unfold plateauFineCoefficient coldExactFine coldFineAtRoot coldFineRootBase coldFineRootCoeff
  rw [plateau_gram_tail hJ]
  push_cast
  rw [hd,he]
  ring

/-- The replay's list of transport depths is exactly the source even-depth sum. -/
theorem plateau_transport_sum_numeric (J : ℕ) (f : ℕ → ℝ) :
    coldRealListSum (coldTransportIndices (2*J)) f = ∑ k ∈ Finset.range J, f (2*(k+1)) := by
  have hd : 2*J/2 = J := by omega
  unfold coldRealListSum coldTransportIndices
  rw [hd,List.map_map]
  exact cold_range_list_sum _ _

/-- The exact denominator is literally the finite P1--P6 denominator. -/
theorem plateau_denominator_numeric {J : ℕ} (hJ : 1 ≤ J) :
    1+(∑ k ∈ Finset.range J, plateauLagCoefficient (coldCT (2*J):ℝ) (coldCD (2*J):ℝ)
      (1+1/((paramsForLag (2*J)).t:ℝ)) (coldG0 (2*J):ℝ) (coldG1 (2*J):ℝ) (coldXi (2*J):ℝ) k)-
      plateauFineCoefficient (coldCT (2*J):ℝ) (coldG0 (2*J):ℝ) (coldG1 (2*J):ℝ) (coldXi (2*J):ℝ) J =
        coldExactDenominator (2*J) := by
  simp_rw [plateau_lag_numeric]
  rw [plateau_fine_numeric hJ,coldExactDenominator,coldExactQSum,plateau_transport_sum_numeric]

end ASDExplicitGamma.Cold
