module

public import ASDExplicitGamma.Cold.PlateauRecurrenceAlgebra

/-! # The source finite-lag coefficients and fine-tail mass -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The Gram-weight product at the even source depth `2(k+1)`. -/
def plateauGramWeight (g0 g1 ξ : ℝ) (k : ℕ) : ℝ :=
  plateauEvenWeight k*(g0+g1*ξ*(Real.sqrt 3)^(k+1))

/-- The exact coefficient q at even depth `2(k+1)`, with the depth-four recovery term. -/
def plateauLagCoefficient (CT CD α g0 g1 ξ : ℝ) (k : ℕ) : ℝ :=
  2*CT*α*plateauGramWeight g0 g1 ξ k+if k=1 then CD else 0

/-- The exact source fine-tail coefficient, beyond even lag `2J`. -/
def plateauFineCoefficient (CT g0 g1 ξ : ℝ) (J : ℕ) : ℝ :=
  2*CT*(∑' k : ℕ, plateauGramWeight g0 g1 ξ (k+J))

/-- All Gram-weight products are summable. -/
theorem summable_plateauGramWeight (g0 g1 ξ : ℝ) : Summable (plateauGramWeight g0 g1 ξ) := by
  convert (summable_plateauEvenWeight.mul_right g0).add
    (summable_plateauEvenWeight_sqrtThree.mul_left (g1*ξ)) using 1
  funext k
  dsimp [plateauGramWeight]
  ring

/-- The finite coefficient mass includes exactly one copy of the depth-four term. -/
theorem sum_plateauLagCoefficient {J : ℕ} (hJ : 2 ≤ J) (CT CD α g0 g1 ξ : ℝ) :
    (∑ k ∈ Finset.range J, plateauLagCoefficient CT CD α g0 g1 ξ k) =
      2*CT*α*(∑ k ∈ Finset.range J, plateauGramWeight g0 g1 ξ k)+CD := by
  unfold plateauLagCoefficient
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp [Finset.sum_ite_eq',Finset.mem_range,show 1 < J by omega]

/-- The weighted finite means include exactly the depth-four recovery mean. -/
theorem sum_plateauLagCoefficient_mul {J : ℕ} (hJ : 2 ≤ J) (CT CD α g0 g1 ξ : ℝ) (μ : ℕ → ℝ) :
    (∑ k ∈ Finset.range J, plateauLagCoefficient CT CD α g0 g1 ξ k*μ k) =
      2*CT*α*(∑ k ∈ Finset.range J, plateauGramWeight g0 g1 ξ k*μ k)+CD*μ 1 := by
  have he (k : ℕ) : plateauLagCoefficient CT CD α g0 g1 ξ k*μ k =
      (2*CT*α)*(plateauGramWeight g0 g1 ξ k*μ k)+(if k=1 then CD*μ k else 0) := by
    unfold plateauLagCoefficient
    split_ifs <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp [Finset.sum_ite_eq',Finset.mem_range,show 1 < J by omega]

end ASDExplicitGamma.Cold
