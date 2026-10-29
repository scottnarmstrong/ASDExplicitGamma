module

public import ASDExplicitGamma.Cold.ResidualAxialAlgebra

/-! # The actual axial profiles in the residual Poincaré estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The positive or negative first axial frequency. -/
def axialFirst (i : Fin 2) (sign : ℤ) : Fin 2 → ℤ := Pi.single i sign

/-- The higher axial modes which can carry the constant-profile constraint. -/
def axialHighSet (i : Fin 2) : Set (Fin 2 → ℤ) :=
  {p | p (Fin.rev i) = 0 ∧ 9 ≤ (p i) ^ 2}

/-- The two first signed axial modes are distinct. -/
theorem axialFirst_ne (i : Fin 2) : axialFirst i 1 ≠ axialFirst i (-1) := by
  intro h
  have := congrFun h i
  norm_num [axialFirst] at this

/-- First axial frequencies are excluded from the higher-mode set. -/
theorem axialFirst_not_high (i : Fin 2) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    axialFirst i s ∉ axialHighSet i := by
  rcases hs with hs | hs <;> subst s <;> simp [axialHighSet, axialFirst]

/-- The constant-profile coefficients at the first positive mode. -/
theorem squareSineMean_first (Q : TriadicCube 2) (i : Fin 2) :
    squareSineMean Q i (axialFirst i 1) = 2 / Real.pi := by
  rw [squareSineMean_formula]
  fin_cases i <;> norm_num [axialFirst]

/-- The constant-profile coefficients at the first negative mode. -/
theorem squareSineMean_neg_first (Q : TriadicCube 2) (i : Fin 2) :
    squareSineMean Q i (axialFirst i (-1)) = -2 / Real.pi := by
  rw [squareSineMean_formula]
  fin_cases i <;> norm_num [axialFirst, div_neg, neg_div]

/-- A frequency on a coordinate axis is determined by its axial coordinate. -/
theorem axial_eq_first {i : Fin 2} {p : Fin 2 → ℤ} {s : ℤ}
    (hother : p (Fin.rev i) = 0) (hcoord : p i = s) : p = axialFirst i s := by
  fin_cases i <;> ext k <;> fin_cases k <;> simp_all [axialFirst]

/-- Outside the first pair, the constant profile is supported on higher axial modes. -/
theorem squareSineMean_support (Q : TriadicCube 2) (i : Fin 2) (p : Fin 2 → ℤ)
    (hl : p ≠ axialFirst i 1) (hr : p ≠ axialFirst i (-1)) (hhigh : p ∉ axialHighSet i) :
    squareSineMean Q i p = 0 := by
  by_cases hother : p (Fin.rev i) = 0
  · have hlow : (p i) ^ 2 < 9 := by
      simpa only [axialHighSet, mem_ofPred_eq, hother, true_and, not_le] using hhigh
    have hn1 : p i ≠ 1 := fun h => hl (axial_eq_first hother h)
    have hnn1 : p i ≠ -1 := fun h => hr (axial_eq_first hother h)
    have hb : -2 ≤ p i ∧ p i ≤ 2 := by constructor <;> nlinarith only [hlow]
    have hcases : p i = -2 ∨ p i = 0 ∨ p i = 2 := by omega
    rcases hcases with hn | hn | hn
    all_goals rw [squareSineMean_formula, hn]
    all_goals norm_num [Real.cos_two_mul, neg_mul, Real.cos_neg]
  · rw [squareSineMean_formula, ite_eq_right hother, mul_zero]

/-- Negating the first sine frequency negates the corresponding coefficient. -/
theorem squareScalarCoeff_neg_first (Q : TriadicCube 2) (i : Fin 2) (f : Vec 2 → ℝ) :
    squareScalarCoeff Q {i} f (axialFirst i (-1)) =
      -squareScalarCoeff Q {i} f (axialFirst i 1) := by
  have hmode : boxMode (cubeCorner Q) (cubeScaleFactor Q) {i} (axialFirst i (-1)) =
      (fun x => -boxMode (cubeCorner Q) (cubeScaleFactor Q) {i} (axialFirst i 1) x) := by
    have hfreq : axialFirst i (-1) = Function.update (axialFirst i 1) i (-(axialFirst i 1 i)) := by
      ext k
      by_cases hk : k = i <;> simp [axialFirst, hk, Function.update]
    funext x
    rw [hfreq, boxMode_update_neg]
    simp
  unfold squareScalarCoeff
  simp_rw [hmode, neg_mul, integral_neg]

/-- The genuine zero-mean spatial constraint yields the first-axial-mode estimate. -/
theorem residual_axial_bound (Q : TriadicCube 2) (i : Fin 2) {g : Vec 2 → ℝ}
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hmean : ∫ x, g x ∂normalizedCubeMeasure Q = 0) :
    6 * squareScalarCoeff Q {i} g (axialFirst i 1) ^ 2 ≤
      ∑' p, (axialHighSet i).indicator (fun q => squareScalarCoeff Q {i} g q ^ 2) p := by
  have ha := (square_mixed_parseval Q {i} hg).summable
  have hb : HasSum (fun p => squareSineMean Q i p ^ 2) 1 := by
    have h := square_mixed_parseval Q {i} (f := fun _ => (1 : ℝ)) (memLp_const 1)
    simpa [squareSineMean, squareScalarCoeff, integral_const, Measure.real,
      normalizedCubeMeasure_apply_univ] using h
  have hab : HasSum (fun p => squareScalarCoeff Q {i} g p * squareSineMean Q i p) 0 := by
    have h := square_mixed_parseval_pairing Q {i} hg (memLp_const (1 : ℝ))
    simpa only [squareSineMean, mul_one, hmean] using h
  exact residual_axial_first_mode_bound _ _ _ _ _ (axialFirst_ne i)
    (axialFirst_not_high i 1 (Or.inl rfl)) (axialFirst_not_high i (-1) (Or.inr rfl))
    ha hb hab (squareScalarCoeff_neg_first Q i g) (squareSineMean_first Q i)
    (squareSineMean_neg_first Q i) (squareSineMean_support Q i)

end ASDExplicitGamma.Cold
