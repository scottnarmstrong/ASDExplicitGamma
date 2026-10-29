module

public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry

/-! The genuine Hilbert positive-Haar triangle inequality with sum membership. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem main_hilbertIncrement_add {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (n : ℕ) {f g : Vec d → E}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    hilbertCubeIncrement Q n (fun x => f x+g x) = fun x => hilbertCubeIncrement Q n f x+hilbertCubeIncrement Q n g x := by
  cases n with
  | zero => exact hilbertCubeProjection_add Q 0 hf hg
  | succ n =>
      simp only [hilbertCubeIncrement, hilbertCubeProjection_add Q _ hf hg]
      funext x
      exact (sub_add_sub_comm _ _ _ _).symm

 theorem main_hilbertPrimalEnergy_eq_tsum {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (q : ℝ) (f : Vec d → E)
    (hs : Summable (fun n => q^n*hilbertEnergy Q (hilbertCubeIncrement Q n f))) :
    hilbertPrimalEnergy Q q f = ∑' n, q^n*hilbertEnergy Q (hilbertCubeIncrement Q n f) := by
  simpa only [hilbertPrimalEnergy, pow_zero, one_mul] using hs.tsum_eq_zero_add.symm

/-- Positive Haar triangle inequality for arbitrary actual members, with convergence of the sum. -/
theorem main_hilbert_positive_add {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) {f g : Vec d → E}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hPf : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) f)))
    (hPg : Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) g))) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) (fun x => f x+g x))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => f x+g x) ≤ hilbertPositiveHaarNorm Q (Real.sqrt 3) f+hilbertPositiveHaarNorm Q (Real.sqrt 3) g := by
  let q := Real.sqrt 3
  let a := fun n => Real.sqrt (q^n*hilbertEnergy Q (hilbertCubeIncrement Q n f))
  let b := fun n => Real.sqrt (q^n*hilbertEnergy Q (hilbertCubeIncrement Q n g))
  let c := fun n => Real.sqrt (q^n*hilbertEnergy Q (hilbertCubeIncrement Q n (fun x => f x+g x)))
  have hsq (u : Vec d → E) (n : ℕ) : (Real.sqrt (q^n*hilbertEnergy Q (hilbertCubeIncrement Q n u)))^2 = q^n*hilbertEnergy Q (hilbertCubeIncrement Q n u) :=
    Real.sq_sqrt (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (hilbertEnergy_nonneg Q _))
  have hfs : Summable (fun n => q^n*hilbertEnergy Q (hilbertCubeIncrement Q n f)) := (summable_nat_add_iff 1).1 hPf
  have hgs : Summable (fun n => q^n*hilbertEnergy Q (hilbertCubeIncrement Q n g)) := (summable_nat_add_iff 1).1 hPg
  have has : Summable (fun n => (a n)^2) := by simpa only [a, hsq] using hfs
  have hbs : Summable (fun n => (b n)^2) := by simpa only [b, hsq] using hgs
  have hpoint (n : ℕ) : c n ≤ a n+b n := by
    have h := hilbertL2Norm_add_le Q (hilbertCubeIncrement_memLp Q n f) (hilbertCubeIncrement_memLp Q n g)
    simp only [hilbertL2Norm] at h
    dsimp [a,b,c]
    rw [main_hilbertIncrement_add Q n hf hg]
    rw [Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) n), Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) n),
      Real.sqrt_mul (pow_nonneg (Real.sqrt_nonneg _) n)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (q^n))
  have h := sqrt_tsum_sq_le_of_pointwise has hbs (fun n => Real.sqrt_nonneg _) hpoint
  have hcs : Summable (fun n => q^n*hilbertEnergy Q (hilbertCubeIncrement Q n (fun x => f x+g x))) := by
    simpa only [c, hsq] using h.1
  refine ⟨(summable_nat_add_iff 1).2 hcs, ?_⟩
  have heqa : (∑' n, (a n)^2) = hilbertPrimalEnergy Q q f := by simp only [a, hsq]; exact (main_hilbertPrimalEnergy_eq_tsum Q q f hfs).symm
  have heqb : (∑' n, (b n)^2) = hilbertPrimalEnergy Q q g := by simp only [b, hsq]; exact (main_hilbertPrimalEnergy_eq_tsum Q q g hgs).symm
  have heqc : (∑' n, (c n)^2) = hilbertPrimalEnergy Q q (fun x => f x+g x) := by simp only [c, hsq]; exact (main_hilbertPrimalEnergy_eq_tsum Q q _ hcs).symm
  have hroot : Real.sqrt (∑' n, (c n)^2) ≤ Real.sqrt (∑' n, (a n)^2)+Real.sqrt (∑' n, (b n)^2) := h.2
  rw [heqa, heqb, heqc] at hroot
  exact hroot


end
end ASDExplicitGamma.Main
