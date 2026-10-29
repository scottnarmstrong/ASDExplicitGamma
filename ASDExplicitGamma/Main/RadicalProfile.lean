module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! The scalar affine-radical profile behind the main error function. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set

/-- A positive linear combination of decreasing affine radicals. -/
noncomputable def mainRadicalProfile {ι : Type*} [Fintype ι]
    (c slope : ℝ) (weight offset rate : ι → ℝ) (f : ℝ) : ℝ :=
  c - slope * f + ∑ i, weight i * Real.sqrt (offset i - rate i * f)

/-- The domain is determined by the actual radicands. -/
def mainRadicalDomain {ι : Type*} (offset rate : ι → ℝ) : Set ℝ :=
  {f | ∀ i, 0 ≤ offset i - rate i * f}

theorem mainRadicalDomain_convex {ι : Type*} (offset rate : ι → ℝ) :
    Convex ℝ (mainRadicalDomain offset rate) := by
  intro x hx y hy a b ha hb hab i
  change 0 ≤ offset i - rate i * (a * x + b * y)
  have h := add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
  have heq : offset i - rate i * (a * x + b * y) =
      a * (offset i - rate i * x) + b * (offset i - rate i * y) := by
    calc
      _ = (a+b)*offset i - rate i*(a*x+b*y) := by rw [hab, one_mul]
      _ = _ := by ring
  rw [heq]
  exact h

/-- Concavity follows on the entire closed radicand domain, including its
boundary. No differentiability at a vanishing radicand is needed. -/
theorem mainRadicalProfile_concave {ι : Type*} [Fintype ι]
    (c slope : ℝ) (weight offset rate : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    ConcaveOn ℝ (mainRadicalDomain offset rate) (mainRadicalProfile c slope weight offset rate) := by
  refine ⟨mainRadicalDomain_convex offset rate, ?_⟩
  intro x hx y hy a b ha hb hab
  have hroot (i : ι) : Real.sqrt (offset i - rate i * (a * x + b * y)) ≥
      a * Real.sqrt (offset i - rate i * x) + b * Real.sqrt (offset i - rate i * y) := by
    have h := Real.strictConcaveOn_sqrt.concaveOn.2 (hx i) (hy i) ha hb hab
    have heq : offset i - rate i * (a * x + b * y) =
        a * (offset i - rate i * x) + b * (offset i - rate i * y) := by
      calc
        _ = (a+b)*offset i - rate i*(a*x+b*y) := by rw [hab, one_mul]
        _ = _ := by ring
    rw [heq]
    exact h
  have hsum : a * (∑ i, weight i * Real.sqrt (offset i - rate i * x)) +
      b * (∑ i, weight i * Real.sqrt (offset i - rate i * y)) ≤
      ∑ i, weight i * Real.sqrt (offset i - rate i * (a*x+b*y)) := by
    calc
      _ = ∑ i, weight i * (a * Real.sqrt (offset i-rate i*x) +
          b * Real.sqrt (offset i-rate i*y)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hroot i) (hw i)
  have hlin : c - slope*(a*x+b*y) = a*(c-slope*x)+b*(c-slope*y) := by
    calc
      _ = (a+b)*c - slope*(a*x+b*y) := by rw [hab, one_mul]
      _ = _ := by ring
  simp only [mainRadicalProfile, smul_eq_mul]
  rw [hlin]
  linarith only [hsum]

/-- The same closed profile is nonincreasing when its rates and affine
slope are nonnegative. -/
theorem mainRadicalProfile_antitone {ι : Type*} [Fintype ι]
    (c slope : ℝ) (weight offset rate : ι → ℝ)
    (hs : 0 ≤ slope) (hw : ∀ i, 0 ≤ weight i) (hr : ∀ i, 0 ≤ rate i) :
    Antitone (mainRadicalProfile c slope weight offset rate) := by
  intro x y hxy
  have hsum : (∑ i, weight i * Real.sqrt (offset i - rate i * y)) ≤
      ∑ i, weight i * Real.sqrt (offset i - rate i * x) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i)
    apply Real.sqrt_le_sqrt
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hxy (hr i)) _
  unfold mainRadicalProfile
  have hlin := mul_le_mul_of_nonneg_left hxy hs
  linarith only [hsum, hlin]

end ASDExplicitGamma.Main
