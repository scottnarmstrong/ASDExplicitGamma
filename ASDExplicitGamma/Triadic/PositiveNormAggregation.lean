module

public import ASDExplicitGamma.Triadic.VectorPositiveMultiplier

/-! Exact finite and broken-norm aggregation of three sharp row-product terms. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem sqrt_finset_energy_bound_three {I : Type*} (s : Finset I) (E F G H : I → ℝ) {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hF : ∀ i ∈ s, 0 ≤ F i) (hG : ∀ i ∈ s, 0 ≤ G i) (hH : ∀ i ∈ s, 0 ≤ H i)
    (hb : ∀ i ∈ s, Real.sqrt (E i) ≤ A*Real.sqrt (F i)+B*Real.sqrt (G i)+C*Real.sqrt (H i)) :
    Real.sqrt (∑ i ∈ s, E i) ≤ A*Real.sqrt (∑ i ∈ s, F i)+B*Real.sqrt (∑ i ∈ s, G i)+C*Real.sqrt (∑ i ∈ s, H i) := by
  let T := fun i => (A*Real.sqrt (F i)+B*Real.sqrt (G i))^2
  have ht : Real.sqrt (∑ i ∈ s, T i) ≤ A*Real.sqrt (∑ i ∈ s, F i)+B*Real.sqrt (∑ i ∈ s, G i) := by
    apply sqrt_finset_energy_bound s T F G hA hB (fun i _ => sq_nonneg _) hF hG
    intro i _
    exact le_of_eq (Real.sqrt_sq (add_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (mul_nonneg hB (Real.sqrt_nonneg _))))
  have he := sqrt_finset_energy_bound s E T H (by norm_num : (0:ℝ) ≤ 1) hC hE
    (fun i _ => sq_nonneg _) hH (fun i hi => by
      simpa only [one_mul, T, Real.sqrt_sq (add_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (mul_nonneg hB (Real.sqrt_nonneg _)))] using hb i hi)
  simp only [one_mul] at he
  linarith only [he, ht]

 theorem sqrt_descendantsAverage_energy_bound_three {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (E F G H : TriadicCube d → ℝ) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hE : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ E R) (hF : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ F R)
    (hG : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ G R) (hH : ∀ R ∈ descendantsAtDepth Q j, 0 ≤ H R)
    (hb : ∀ R ∈ descendantsAtDepth Q j, Real.sqrt (E R) ≤ A*Real.sqrt (F R)+B*Real.sqrt (G R)+C*Real.sqrt (H R)) :
    Real.sqrt (descendantsAverage Q j E) ≤ A*Real.sqrt (descendantsAverage Q j F)+
      B*Real.sqrt (descendantsAverage Q j G)+C*Real.sqrt (descendantsAverage Q j H) := by
  have h := sqrt_finset_energy_bound_three (descendantsAtDepth Q j) E F G H hA hB hC hE hF hG hH hb
  unfold descendantsAverage
  simp only [Real.sqrt_mul (inv_nonneg.mpr (Nat.cast_nonneg (descendantsAtDepth Q j).card))]
  have hw := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (((descendantsAtDepth Q j).card:ℝ)⁻¹))
  convert hw using 1
  ring

end
end ASDExplicitGamma.Triadic
