module

public import ASDExplicitGamma.Triadic.HilbertProductSequence
public import ASDExplicitGamma.Triadic.HilbertL2Bounds
public import ASDExplicitGamma.Triadic.VectorHaar

/-! Exact Haar norm triangle inequalities with proved convergence of sums. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem sqrt_finset_sq_add_le {I : Type*} (s : Finset I) (a b : I → ℝ) :
    Real.sqrt (∑ i ∈ s, (a i+b i)^2) ≤ Real.sqrt (∑ i ∈ s, (a i)^2)+Real.sqrt (∑ i ∈ s, (b i)^2) := by
  have heq : (∑ i ∈ s, (a i+b i)^2) = (∑ i ∈ s, (a i)^2)+2*(∑ i ∈ s, a i*b i)+(∑ i ∈ s, (b i)^2) := by
    simp only [add_sq, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  apply (Real.sqrt_le_iff).2
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have ha := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (a i)) : 0 ≤ ∑ i ∈ s, (a i)^2)
  have hb := Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)) : 0 ≤ ∑ i ∈ s, (b i)^2)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s a b
  nlinarith only [heq, ha, hb, hcs]

 theorem sqrt_tsum_sq_le_of_pointwise {a b c : ℕ → ℝ}
    (ha : Summable (fun n => (a n)^2)) (hb : Summable (fun n => (b n)^2))
    (hc : ∀ n, 0 ≤ c n) (hbound : ∀ n, c n ≤ a n+b n) :
    Summable (fun n => (c n)^2) ∧ Real.sqrt (∑' n, (c n)^2) ≤
      Real.sqrt (∑' n, (a n)^2)+Real.sqrt (∑' n, (b n)^2) := by
  have hadd : Summable (fun n => (a n+b n)^2) :=
    ((ha.mul_left 2).add (hb.mul_left 2)).of_nonneg_of_le (fun n => sq_nonneg _) (fun n => by nlinarith only [sq_nonneg (a n-b n)])
  have hsq (n : ℕ) : (c n)^2 ≤ (a n+b n)^2 := pow_le_pow_left₀ (hc n) (hbound n) 2
  have hs : Summable (fun n => (c n)^2) := hadd.of_nonneg_of_le (fun n => sq_nonneg _) hsq
  exact ⟨hs, (Real.sqrt_le_sqrt (hs.tsum_le_tsum hsq hadd)).trans (sqrt_tsum_sq_add_le a b ha hb)⟩

 theorem cubeIncrement_add_of_memLp {d : ℕ} (Q : TriadicCube d) (n : ℕ) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeIncrement Q n (fun x => f x+g x) = fun x => cubeIncrement Q n f x+cubeIncrement Q n g x := by
  cases n with
  | zero => exact projection_add Q 0 hf hg
  | succ n =>
      simp only [cubeIncrement, projection_add Q _ hf hg]
      funext x
      exact (sub_add_sub_comm _ _ _ _).symm

 theorem primalEnergy_eq_tsum {d : ℕ} (Q : TriadicCube d) (q : ℝ) (f : Vec d → ℝ)
    (hs : Summable (fun n => q^n*energy Q (cubeIncrement Q n f))) :
    primalEnergy Q q f = ∑' n, q^n*energy Q (cubeIncrement Q n f) := by
  simpa only [primalEnergy, pow_zero, one_mul] using hs.tsum_eq_zero_add.symm

/-- Positive Haar triangle inequality for arbitrary actual members, with convergence of the sum. -/
theorem positiveHaarNorm_add_le {d : ℕ} (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hPf : Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) f)))
    (hPg : Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) g))) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => f x+g x))) ∧
    positiveHaarNorm Q (fun x => f x+g x) ≤ positiveHaarNorm Q f+positiveHaarNorm Q g := by
  let q := Real.sqrt 3
  let a := fun n => Real.sqrt (q^n*energy Q (cubeIncrement Q n f))
  let b := fun n => Real.sqrt (q^n*energy Q (cubeIncrement Q n g))
  let c := fun n => Real.sqrt (q^n*energy Q (cubeIncrement Q n (fun x => f x+g x)))
  have hsq (u : Vec d → ℝ) (n : ℕ) : (Real.sqrt (q^n*energy Q (cubeIncrement Q n u)))^2 = q^n*energy Q (cubeIncrement Q n u) :=
    Real.sq_sqrt (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (energy_nonneg Q _))
  have hfs : Summable (fun n => q^n*energy Q (cubeIncrement Q n f)) := (summable_nat_add_iff 1).1 hPf
  have hgs : Summable (fun n => q^n*energy Q (cubeIncrement Q n g)) := (summable_nat_add_iff 1).1 hPg
  have has : Summable (fun n => (a n)^2) := by simpa only [a, hsq] using hfs
  have hbs : Summable (fun n => (b n)^2) := by simpa only [b, hsq] using hgs
  have hpoint (n : ℕ) : c n ≤ a n+b n := by
    have h := hilbertL2Norm_add_le Q (increment_memLp Q n f) (increment_memLp Q n g)
    simp only [hilbertL2Norm, hilbertEnergy_real] at h
    dsimp [a,b,c]
    rw [cubeIncrement_add_of_memLp Q n hf hg]
    rw [Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) n), Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) n),
      Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) n)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (q^n))
  have h := sqrt_tsum_sq_le_of_pointwise has hbs (fun n => Real.sqrt_nonneg _) hpoint
  have hcs : Summable (fun n => q^n*energy Q (cubeIncrement Q n (fun x => f x+g x))) := by
    simpa only [c, hsq] using h.1
  refine ⟨(summable_nat_add_iff 1).2 hcs, ?_⟩
  have heqa : (∑' n, (a n)^2) = primalEnergy Q q f := by simp only [a, hsq]; exact (primalEnergy_eq_tsum Q q f hfs).symm
  have heqb : (∑' n, (b n)^2) = primalEnergy Q q g := by simp only [b, hsq]; exact (primalEnergy_eq_tsum Q q g hgs).symm
  have heqc : (∑' n, (c n)^2) = primalEnergy Q q (fun x => f x+g x) := by simp only [c, hsq]; exact (primalEnergy_eq_tsum Q q _ hcs).symm
  have hroot : Real.sqrt (∑' n, (c n)^2) ≤ Real.sqrt (∑' n, (a n)^2)+Real.sqrt (∑' n, (b n)^2) := h.2
  rw [heqa, heqb, heqc] at hroot
  exact hroot

end
end ASDExplicitGamma.Triadic
