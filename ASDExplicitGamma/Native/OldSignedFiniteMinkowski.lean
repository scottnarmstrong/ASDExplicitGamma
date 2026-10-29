module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity

/-! Finite Euclidean aggregation without loss from the coordinate count. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Finite Minkowski combined with a nonnegative pointwise bound. -/
theorem old_signed_finite_sqrt_sq_bound {I : Type*} [Fintype I]
    (a b c : I → ℝ) (hc : ∀ i,0≤c i) (h : ∀ i,c i≤a i+b i) :
    Real.sqrt (∑ i,c i^2)≤Real.sqrt (∑ i,a i^2)+Real.sqrt (∑ i,b i^2) := by
  let A : EuclideanSpace ℝ I := WithLp.toLp 2 a
  let B : EuclideanSpace ℝ I := WithLp.toLp 2 b
  have hn (f : I → ℝ) : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ I)‖=Real.sqrt (∑ i,f i^2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  have hab : A+B=(WithLp.toLp 2 (fun i => a i+b i) : EuclideanSpace ℝ I) := rfl
  calc
    _ ≤ Real.sqrt (∑ i,(a i+b i)^2) := Real.sqrt_le_sqrt
      (Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hc i) (h i) 2))
    _ = ‖A+B‖ := by rw [hab,hn]
    _ ≤ ‖A‖+‖B‖ := norm_add_le A B
    _ = _ := by rw [hn,hn]

/-- A common pair of nonnegative coefficients factors out of the exact
finite Euclidean bill, preserving all joint coordinate information. -/
theorem old_signed_finite_sqrt_energy_bound {I : Type*} [Fintype I]
    (E G c : I → ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hE : ∀ i,0≤E i) (hG : ∀ i,0≤G i) (hc : ∀ i,0≤c i)
    (h : ∀ i,c i≤A*Real.sqrt (E i)+B*Real.sqrt (G i)) :
    Real.sqrt (∑ i,c i^2)≤A*Real.sqrt (∑ i,E i)+B*Real.sqrt (∑ i,G i) := by
  have hh := old_signed_finite_sqrt_sq_bound
    (fun i => A*Real.sqrt (E i)) (fun i => B*Real.sqrt (G i)) c hc h
  simp_rw [mul_pow,Real.sq_sqrt (hE _),Real.sq_sqrt (hG _)] at hh
  rw [←Finset.mul_sum,←Finset.mul_sum,Real.sqrt_mul (sq_nonneg A),Real.sqrt_sq hA,
    Real.sqrt_mul (sq_nonneg B),Real.sqrt_sq hB] at hh
  exact hh

/-- Weighted finite Minkowski for actual cell averages. -/
theorem old_signed_finite_weighted_sqrt_energy_bound {I : Type*} [Fintype I]
    (w E G c : I → ℝ) {A B : ℝ} (hw : ∀ i,0≤w i) (hA : 0≤A) (hB : 0≤B)
    (hE : ∀ i,0≤E i) (hG : ∀ i,0≤G i) (hc : ∀ i,0≤c i)
    (h : ∀ i,c i≤A*Real.sqrt (E i)+B*Real.sqrt (G i)) :
    Real.sqrt (∑ i,w i*c i^2)≤A*Real.sqrt (∑ i,w i*E i)+B*Real.sqrt (∑ i,w i*G i) := by
  have hh := old_signed_finite_sqrt_energy_bound
    (fun i => w i*E i) (fun i => w i*G i) (fun i => Real.sqrt (w i)*c i) hA hB
    (fun i => mul_nonneg (hw i) (hE i)) (fun i => mul_nonneg (hw i) (hG i))
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hc i)) (fun i => ?_)
  · simp_rw [mul_pow,Real.sq_sqrt (hw _)] at hh
    exact hh
  · rw [Real.sqrt_mul (hw i),Real.sqrt_mul (hw i)]
    exact (mul_le_mul_of_nonneg_left (h i) (Real.sqrt_nonneg _)).trans_eq (by ring)

end
end ASDExplicitGamma.Native
