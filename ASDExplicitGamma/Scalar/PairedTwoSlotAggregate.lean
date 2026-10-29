module

public import ASDExplicitGamma.Variational.LemmaVTiles

/-! The cell aggregation of the two-slot bound (pure real analysis over a tiling). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Triadic

noncomputable section

theorem cell_pair_cs (a b p q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * p + b * q ≤ Real.sqrt ((a ^ 2 + b ^ 2) * (p ^ 2 + q ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (a * q - b * p)]

/-- Cauchy--Schwarz for descendant averages. -/
theorem average_sqrt_cs (Q : TriadicCube 2) (n : ℕ) (E W : TriadicCube 2 → ℝ)
    (hE : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ E R) (hW : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ W R) :
    descendantsAverage Q n (fun R => Real.sqrt (E R) * Real.sqrt (W R)) ≤
      Real.sqrt (descendantsAverage Q n E) * Real.sqrt (descendantsAverage Q n W) := by
  classical
  set D := descendantsAtDepth Q n with hD
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D (fun R => Real.sqrt (E R))
    (fun R => Real.sqrt (W R))
  have hEs : ∑ R ∈ D, Real.sqrt (E R) ^ 2 = ∑ R ∈ D, E R :=
    Finset.sum_congr rfl fun R hR => Real.sq_sqrt (hE R hR)
  have hWs : ∑ R ∈ D, Real.sqrt (W R) ^ 2 = ∑ R ∈ D, W R :=
    Finset.sum_congr rfl fun R hR => Real.sq_sqrt (hW R hR)
  rw [hEs, hWs] at hcs
  unfold descendantsAverage
  have hAE : 0 ≤ ((D.card : ℝ))⁻¹ * ∑ R ∈ D, E R :=
    mul_nonneg (by positivity) (Finset.sum_nonneg hE)
  rw [← Real.sqrt_mul hAE]
  have hn : 0 ≤ ((D.card : ℝ))⁻¹ := by positivity
  have hS : 0 ≤ ∑ R ∈ D, Real.sqrt (E R) * Real.sqrt (W R) :=
    Finset.sum_nonneg fun R _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply Real.le_sqrt_of_sq_le
  have h1 : (((D.card : ℝ))⁻¹ * ∑ R ∈ D, Real.sqrt (E R) * Real.sqrt (W R)) ^ 2 =
      ((D.card : ℝ))⁻¹ ^ 2 * (∑ R ∈ D, Real.sqrt (E R) * Real.sqrt (W R)) ^ 2 := by ring
  rw [h1]
  calc _ ≤ ((D.card : ℝ))⁻¹ ^ 2 * ((∑ R ∈ D, E R) * ∑ R ∈ D, W R) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

theorem cell_aggregation (Q : TriadicCube 2) (n : ℕ)
    (t X Y B E pF pG : TriadicCube 2 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hX : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ X R)
    (hY : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ Y R)
    (hB : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ B R)
    (hE : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ E R)
    (hpF : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ pF R)
    (hpG : ∀ R ∈ descendantsAtDepth Q n, 0 ≤ pG R)
    (hXY : ∀ R ∈ descendantsAtDepth Q n, X R + Y R ≤ B R * E R)
    (ht : ∀ R ∈ descendantsAtDepth Q n,
      t R ≤ Real.sqrt (Y R) * pF R + Real.sqrt (X R) * pG R + 2 * c * (B R * (pF R * pG R))) :
    descendantsAverage Q n t ≤
      Real.sqrt (descendantsAverage Q n E) *
        Real.sqrt (descendantsAverage Q n (fun R => B R * (pF R ^ 2 + pG R ^ 2))) +
      2 * c * descendantsAverage Q n (fun R => B R * (pF R * pG R)) := by
  have hcell : ∀ R ∈ descendantsAtDepth Q n,
      t R ≤ Real.sqrt (E R) * Real.sqrt (B R * (pF R ^ 2 + pG R ^ 2)) +
        2 * c * (B R * (pF R * pG R)) := by
    intro R hR
    have h1 := cell_pair_cs (Real.sqrt (Y R)) (Real.sqrt (X R)) (pF R) (pG R)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (hY R hR), Real.sq_sqrt (hX R hR)] at h1
    have h2 : Real.sqrt ((Y R + X R) * (pF R ^ 2 + pG R ^ 2)) ≤
        Real.sqrt (E R) * Real.sqrt (B R * (pF R ^ 2 + pG R ^ 2)) := by
      rw [← Real.sqrt_mul (hE R hR)]
      apply Real.sqrt_le_sqrt
      have := hXY R hR
      have hw : 0 ≤ pF R ^ 2 + pG R ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hw]
    linarith [ht R hR]
  have h1 := descendantsAverage_le (Q := Q) (j := n) hcell
  have hsum : descendantsAverage Q n (fun R => Real.sqrt (E R) *
        Real.sqrt (B R * (pF R ^ 2 + pG R ^ 2)) + 2 * c * (B R * (pF R * pG R))) =
      descendantsAverage Q n (fun R => Real.sqrt (E R) *
        Real.sqrt (B R * (pF R ^ 2 + pG R ^ 2))) +
      2 * c * descendantsAverage Q n (fun R => B R * (pF R * pG R)) := by
    rw [descendantsAverage_add, descendantsAverage_mul_left]
  have h3 := average_sqrt_cs Q n E (fun R => B R * (pF R ^ 2 + pG R ^ 2)) hE
    (fun R hR => mul_nonneg (hB R hR) (by positivity))
  linarith

end

end ASDExplicitGamma.Scalar
