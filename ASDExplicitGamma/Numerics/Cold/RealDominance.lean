module

public import ASDExplicitGamma.Numerics.Cold.HistoryCertificate
public import Mathlib.Algebra.Group.Nat.Even

/-! Real comparison lemmas for the exact, unrounded cold update. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

/-- The radical replacement from NU-CO-SQRT3-BOUND, raised to any natural power. -/
theorem cold_sqrtThree_pow_le (n : ℕ) :
    (Real.sqrt 3) ^ n ≤ (26 / 15 : ℝ) ^ n := by
  have hroot : Real.sqrt 3 ≤ (26 / 15 : ℝ) :=
    le_of_lt sqrtThree_lt_twentySixOverFifteen
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hroot (Real.sqrt_nonneg 3)
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 26/15) n)

/-- Monotonicity of the geometric tail factor on `[0,1)`. -/
theorem cold_geometric_ratio_mono {z w : ℝ} {n : ℕ}
    (hz : 0 ≤ z) (hzw : z ≤ w) (hw : w < 1) :
    z ^ n / (1-z) ≤ w ^ n / (1-w) := by
  have hpow : z ^ n ≤ w ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hzw hz (pow_nonneg (le_trans hz hzw) n)
  have hzDen : 0 < 1-z := by linarith
  have hwDen : 0 < 1-w := by linarith
  calc
    z ^ n / (1-z) ≤ w ^ n / (1-z) :=
      div_le_div_of_nonneg_right hpow (by linarith)
    _ ≤ w ^ n / (1-w) := by
      apply (div_le_div_iff₀ hzDen hwDen).2
      exact mul_le_mul_of_nonneg_left (by linarith)
        (pow_nonneg (le_trans hz hzw) n)

/-- A real-valued finite sum, kept separate from the rational replay's accumulator. -/
def coldRealListSum {α : Type} (xs : List α) (f : α → ℝ) : ℝ := (xs.map f).sum

theorem coldListSum_add_initial (xs : List ℕ) (f : ℕ → ℚ) (c : ℚ) :
    xs.foldl (fun acc i => acc + f i) c = c + coldListSum xs f := by
  induction xs generalizing c with
  | nil => simp [coldListSum]
  | cons a xs ih =>
      simp only [coldListSum, List.foldl_cons, zero_add]
      rw [ih (c + f a), ih (f a)]
      ring

theorem coldRealListSum_cast (xs : List ℕ) (f : ℕ → ℚ) :
    coldRealListSum xs (fun i => (f i : ℝ)) = (coldListSum xs f : ℝ) := by
  induction xs with
  | nil => simp [coldRealListSum, coldListSum]
  | cons a xs ih =>
      simp only [coldListSum, List.foldl_cons, zero_add]
      change (f a : ℝ) + coldRealListSum xs (fun i => (f i : ℝ)) =
        ((xs.foldl (fun acc i => acc + f i) (f a) : ℚ) : ℝ)
      rw [ih]
      rw [coldListSum_add_initial]
      push_cast
      ring

theorem coldRealListSum_add {α : Type} (xs : List α) (f g : α → ℝ) :
    coldRealListSum xs (fun x => f x + g x) =
      coldRealListSum xs f + coldRealListSum xs g := by
  induction xs with
  | nil => simp [coldRealListSum]
  | cons a xs ih =>
      change f a + g a + coldRealListSum xs (fun x => f x + g x) =
        (f a + coldRealListSum xs f) + (g a + coldRealListSum xs g)
      rw [ih]
      ring

theorem coldRealListSum_const_mul {α : Type} (xs : List α) (c : ℝ) (f : α → ℝ) :
    coldRealListSum xs (fun x => c * f x) = c * coldRealListSum xs f := by
  induction xs with
  | nil => simp [coldRealListSum]
  | cons a xs ih =>
      change c * f a + coldRealListSum xs (fun x => c * f x) =
        c * (f a + coldRealListSum xs f)
      rw [ih]
      ring

theorem coldRealListSum_mono {α : Type} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : coldRealListSum xs f ≤ coldRealListSum xs g := by
  induction xs with
  | nil => simp [coldRealListSum]
  | cons a xs ih =>
      simp only [coldRealListSum, List.map_cons, List.sum_cons]
      apply add_le_add
      · exact h a (by simp)
      · apply ih
        intro x hx
        exact h x (by simp [hx])

theorem coldRealListSum_nonneg {α : Type} (xs : List α) (f : α → ℝ)
    (h : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ coldRealListSum xs f := by
  have := coldRealListSum_mono xs (fun _ => 0) f (by intro x hx; exact h x hx)
  simpa [coldRealListSum] using this

/-- The update after adding one nonnegative transport weight.  If the new weighted input is at
least the previous-lag cap, the minimum with that cap is monotone in the weight. -/
theorem cold_min_ratio_add_weights_mono
    (p A D q dq dx : ℝ)
    (hD : 0 < D) (hq : 0 ≤ q) (hdq : 0 ≤ dq)
    (hdx : p * dq ≤ dx) :
    min p (A / (D + q)) ≤ min p ((A + dx) / (D + q + dq)) := by
  have hden : 0 < D + q := by linarith
  have hden' : 0 < D + q + dq := by linarith
  by_cases h : A / (D + q) ≤ p
  · have hA : A ≤ p * (D + q) := (div_le_iff₀ hden).mp h
    have hcross₁ : 0 ≤ (dx - p*dq) * (D+q) :=
      mul_nonneg (sub_nonneg.mpr hdx) (le_of_lt hden)
    have hcross₂ : 0 ≤ (p*(D+q)-A) * dq :=
      mul_nonneg (sub_nonneg.mpr hA) hdq
    have hratio : A / (D + q) ≤ (A + dx) / (D + q + dq) := by
      rw [div_le_div_iff₀ hden hden']
      nlinarith [hcross₁, hcross₂]
    apply le_min
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans hratio
  · have hR : p < A / (D + q) := lt_of_not_ge h
    have hA : p * (D + q) ≤ A := (le_div_iff₀ hden).mp (le_of_lt hR)
    have hA' : p * (D + q + dq) ≤ A + dx := by nlinarith [hA, hdx]
    have hR' : p ≤ (A + dx) / (D + q + dq) := (le_div_iff₀ hden').mpr hA'
    rw [min_eq_left (le_of_lt hR), min_eq_left hR']

/-- Simultaneously increasing transport weights increases the capped ratio, provided every
transported mean is at least the cap used by the outer `min`. -/
theorem cold_min_weighted_ratio_mono
    {α : Type} (p N D : ℝ) (xs : List α)
    (q q' x : α → ℝ)
    (hden : 0 < D + coldRealListSum xs q)
    (hqq : ∀ i ∈ xs, q i ≤ q' i)
    (hxp : ∀ i ∈ xs, p ≤ x i) :
    min p ((N + coldRealListSum xs (fun i => q i * x i)) /
      (D + coldRealListSum xs q)) ≤
    min p ((N + coldRealListSum xs (fun i => q' i * x i)) /
      (D + coldRealListSum xs q')) := by
  let dq : α → ℝ := fun i => q' i - q i
  let dx : α → ℝ := fun i => dq i * x i
  have hdq_nonneg : 0 ≤ coldRealListSum xs dq :=
    coldRealListSum_nonneg xs dq (by
      intro i hi
      exact sub_nonneg.mpr (hqq i hi))
  have hdx_mono : coldRealListSum xs (fun i => p * dq i) ≤
      coldRealListSum xs dx := coldRealListSum_mono xs _ _ (by
        intro i hi
        have hqdiff : 0 ≤ dq i := sub_nonneg.mpr (hqq i hi)
        have hxdiff : 0 ≤ x i - p := sub_nonneg.mpr (hxp i hi)
        have hprod := mul_nonneg hqdiff hxdiff
        dsimp [dx, dq]
        nlinarith)
  have hscale : coldRealListSum xs (fun i => p * dq i) =
      p * coldRealListSum xs dq := coldRealListSum_const_mul xs p dq
  have hdeltaX : p * coldRealListSum xs dq ≤ coldRealListSum xs dx := by
    rw [← hscale]
    exact hdx_mono
  have hQ : coldRealListSum xs q + coldRealListSum xs dq =
      coldRealListSum xs q' := by
    calc
      _ = coldRealListSum xs (fun i => q i + dq i) :=
        (coldRealListSum_add xs q dq).symm
      _ = _ := by
        congr 1
        funext i
        dsimp [dq]
        ring
  have hX : coldRealListSum xs (fun i => q i * x i) +
      coldRealListSum xs dx = coldRealListSum xs (fun i => q' i * x i) := by
    calc
      _ = coldRealListSum xs (fun i => q i * x i + dx i) :=
        (coldRealListSum_add xs (fun i => q i * x i) dx).symm
      _ = _ := by
        congr 1
        funext i
        dsimp [dx, dq]
        ring
  have hstep := cold_min_ratio_add_weights_mono p
    (N + coldRealListSum xs (fun i => q i * x i))
    (D + coldRealListSum xs q) 0
    (coldRealListSum xs dq) (coldRealListSum xs dx)
    hden (by norm_num) hdq_nonneg hdeltaX
  simpa [add_assoc, hQ, hX] using hstep

/-- Increasing the transported means increases the capped update when the weights are
nonnegative. -/
theorem cold_min_weighted_means_mono
    {α : Type} (p N D : ℝ) (xs : List α)
    (q x y : α → ℝ)
    (hden : 0 < D + coldRealListSum xs q) (hq : ∀ i ∈ xs, 0 ≤ q i)
    (hxy : ∀ i ∈ xs, x i ≤ y i) :
    min p ((N + coldRealListSum xs (fun i => q i * x i)) /
      (D + coldRealListSum xs q)) ≤
    min p ((N + coldRealListSum xs (fun i => q i * y i)) /
      (D + coldRealListSum xs q)) := by
  have hqsum : 0 ≤ coldRealListSum xs q := coldRealListSum_nonneg xs q hq
  have hnum : coldRealListSum xs (fun i => q i * x i) ≤
      coldRealListSum xs (fun i => q i * y i) :=
    coldRealListSum_mono xs _ _ (by
      intro i hi
      exact mul_le_mul_of_nonneg_left (hxy i hi) (hq i hi))
  have hratio0 := div_le_div_of_nonneg_right
    (add_le_add_left hnum N) (le_of_lt hden)
  have hratio : (N + coldRealListSum xs (fun i => q i * x i)) /
      (D + coldRealListSum xs q) ≤
      (N + coldRealListSum xs (fun i => q i * y i)) /
      (D + coldRealListSum xs q) := by
    simpa [add_comm] using hratio0
  apply le_min
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans hratio

/-- Enlarging the non-transport source and reducing its positive denominator also increases the
capped update. -/
theorem cold_min_ratio_base_mono
    (p N N' D D' X X' : ℝ)
    (hD' : 0 < D') (hDD' : D' ≤ D)
    (hN : 0 ≤ N) (hNN' : N ≤ N') (hX : 0 ≤ X) (hXX' : X ≤ X') :
    min p ((N + X) / D) ≤ min p ((N' + X') / D') := by
  have hnum : 0 ≤ N + X := by linarith
  have hden : 0 < D := lt_of_lt_of_le hD' (by linarith)
  have hratio : (N + X) / D ≤ (N' + X') / D' := by
    rw [div_le_div_iff₀ hden hD']
    have hsum : N + X ≤ N' + X' := add_le_add hNN' hXX'
    have hcross₁ : 0 ≤ ((N' + X') - (N + X)) * D' :=
      mul_nonneg (sub_nonneg.mpr hsum) (le_of_lt hD')
    have hcross₂ : 0 ≤ (N + X) * (D - D') :=
      mul_nonneg hnum (sub_nonneg.mpr hDD')
    nlinarith [hcross₁, hcross₂]
  apply le_min
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans hratio

/-- Rational part of `q_r`, split into its root-free part and its radical coefficient.
The coefficients are those of NU-CO-COLD-LAGS. -/
def coldQRootBase (j r : ℕ) : ℚ :=
  2 * coldCT j * (1 + 1 / (paramsForLag j).t) * coldG0 j * coldWeight r +
    if r = 4 then coldCD j else 0

def coldQRootCoeff (j r : ℕ) : ℚ :=
  2 * coldCT j * (1 + 1 / (paramsForLag j).t) *
    coldG1 j * coldXi j * coldWeight r

/-- The exact `q_r` with a real root base `rho` in the fractional-power slot. -/
def coldQAtRoot (j r : ℕ) (rho : ℝ) : ℝ :=
  (coldQRootBase j r : ℝ) + (coldQRootCoeff j r : ℝ) * rho ^ (r / 2)

theorem cold_q_as_root (j r : ℕ) :
    (coldQ j r : ℝ) = coldQAtRoot j r (26 / 15) := by
  unfold coldQ coldQAtRoot coldQRootBase coldQRootCoeff
  push_cast
  ring

theorem cold_q_components_nonneg :
    ∀ j ∈ coldUpdatedLags, ∀ i ∈ List.range (j/2),
      0 ≤ coldQRootBase j (2*(i+1)) ∧ 0 ≤ coldQRootCoeff j (2*(i+1)) := by
  decide +kernel

/-- Monotonicity of the exact transport coefficient in its root input. -/
theorem cold_q_root_mono (j r : ℕ) (rho nu : ℝ)
    (hcoeff : 0 ≤ coldQRootCoeff j r)
    (hpow : rho ^ (r/2) ≤ nu ^ (r/2)) :
    coldQAtRoot j r rho ≤ coldQAtRoot j r nu := by
  unfold coldQAtRoot
  have hcoeffR : (0 : ℝ) ≤ (coldQRootCoeff j r : ℝ) := by exact_mod_cast hcoeff
  simpa [add_comm] using add_le_add_right
    (mul_le_mul_of_nonneg_left hpow hcoeffR) (coldQRootBase j r : ℝ)

noncomputable def coldExactQ (j r : ℕ) : ℝ := coldQAtRoot j r (Real.sqrt 3)

theorem cold_exact_q_le_rational (j r : ℕ)
    (hcoeff : 0 ≤ coldQRootCoeff j r) :
    coldExactQ j r ≤ (coldQ j r : ℝ) := by
  calc
    coldExactQ j r = coldQAtRoot j r (Real.sqrt 3) := rfl
    _ ≤ coldQAtRoot j r (26/15) := cold_q_root_mono j r _ _ hcoeff
      (cold_sqrtThree_pow_le (r/2))
    _ = (coldQ j r : ℝ) := (cold_q_as_root j r).symm

theorem cold_exact_q_ge_base (j r : ℕ)
    (hcoeff : 0 ≤ coldQRootCoeff j r) :
    (coldQRootBase j r : ℝ) ≤ coldExactQ j r := by
  unfold coldExactQ coldQAtRoot
  have hcoeffR : (0 : ℝ) ≤ (coldQRootCoeff j r : ℝ) := by exact_mod_cast hcoeff
  exact le_add_of_nonneg_right (mul_nonneg hcoeffR (pow_nonneg (Real.sqrt_nonneg 3) _))

/-- The tail contribution split into its rational base and its real geometric ratio. -/
def coldFineRootBase (j : ℕ) : ℚ :=
  2 * coldCT j * coldG0 j * (7/2 : ℚ) * (1/3 : ℚ)^j

def coldFineRootCoeff (j : ℕ) : ℚ :=
  2 * coldCT j * coldG1 j * coldXi j * 28

noncomputable def coldFineAtRoot (j : ℕ) (rho : ℝ) : ℝ :=
  (coldFineRootBase j : ℝ) + (coldFineRootCoeff j : ℝ) *
    ((rho/9)^(j/2+1) / (1-rho/9))

noncomputable def coldExactFine (j : ℕ) : ℝ := coldFineAtRoot j (Real.sqrt 3)

theorem cold_fine_as_root (j : ℕ) :
    (coldFineTail j : ℝ) = coldFineAtRoot j (26/15) := by
  unfold coldFineTail coldFineAtRoot coldFineRootBase coldFineRootCoeff
  push_cast
  norm_num
  ring

theorem cold_fine_coeff_nonneg :
    ∀ j ∈ coldUpdatedLags, 0 ≤ coldFineRootCoeff j := by
  decide +kernel

def coldTransportIndices (j : ℕ) : List ℕ :=
  (List.range (j/2)).map (fun i => 2*(i+1))

def coldQRootBaseSum (j : ℕ) : ℚ :=
  coldListSum (coldTransportIndices j) (coldQRootBase j)

noncomputable def coldExactQSum (j : ℕ) : ℝ :=
  coldRealListSum (coldTransportIndices j) (coldExactQ j)

noncomputable def coldExactDenominator (j : ℕ) : ℝ :=
  1 + coldExactQSum j - coldExactFine j

theorem cold_exact_denominator_lower_positive :
    ∀ j ∈ coldUpdatedLags, 0 < 1 + coldQRootBaseSum j - coldFineTail j := by
  decide +kernel

theorem cold_exact_qsum_lower (j : ℕ) (hj : j ∈ coldUpdatedLags) :
    (coldQRootBaseSum j : ℝ) ≤ coldExactQSum j := by
  change (coldListSum (coldTransportIndices j) (coldQRootBase j) : ℝ) ≤ _
  rw [← coldRealListSum_cast (coldTransportIndices j) (coldQRootBase j)]
  apply coldRealListSum_mono
  intro r hr
  rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
  exact cold_exact_q_ge_base j (2*(i+1))
    (cold_q_components_nonneg j hj i hi).2

theorem cold_fine_root_mono (j : ℕ) (hcoeff : 0 ≤ coldFineRootCoeff j) :
    coldFineAtRoot j (Real.sqrt 3) ≤ coldFineAtRoot j (26/15) := by
  have hz0 : 0 ≤ Real.sqrt 3 / 9 := by positivity
  have hzw : Real.sqrt 3 / 9 ≤ (26/15 : ℝ) / 9 := by
    exact div_le_div_of_nonneg_right
      (le_of_lt sqrtThree_lt_twentySixOverFifteen) (by norm_num)
  have hw : (26/15 : ℝ) / 9 < 1 := by norm_num
  have hgeom := cold_geometric_ratio_mono hz0 hzw hw (n := j/2+1)
  have hcoeffR : (0 : ℝ) ≤ (coldFineRootCoeff j : ℝ) := by exact_mod_cast hcoeff
  unfold coldFineAtRoot
  exact add_le_add_right
    (mul_le_mul_of_nonneg_left hgeom hcoeffR) (coldFineRootBase j : ℝ)

theorem cold_exact_fine_le_rational (j : ℕ) (hj : j ∈ coldUpdatedLags) :
    coldExactFine j ≤ (coldFineTail j : ℝ) := by
  calc
    coldExactFine j = coldFineAtRoot j (Real.sqrt 3) := rfl
    _ ≤ coldFineAtRoot j (26/15) := cold_fine_root_mono j (cold_fine_coeff_nonneg j hj)
    _ = (coldFineTail j : ℝ) := (cold_fine_as_root j).symm

theorem cold_exact_denominator_pos (j : ℕ) (hj : j ∈ coldUpdatedLags) :
    0 < coldExactDenominator j := by
  have hq := cold_exact_qsum_lower j hj
  have hF := cold_exact_fine_le_rational j hj
  have hbase : (0 : ℝ) < 1 + (coldQRootBaseSum j : ℝ) - (coldFineTail j : ℝ) := by
    exact_mod_cast cold_exact_denominator_lower_positive j hj
  unfold coldExactDenominator
  linarith

theorem cold_q_nonneg_lags :
    ∀ j ∈ coldUpdatedLags, ∀ i ∈ List.range (j/2),
      0 ≤ (coldQ j (2*(i+1)) : ℝ) := by
  intro j hj i hi
  have hc := cold_q_components_nonneg j hj i hi
  rw [cold_q_as_root j (2*(i+1))]
  unfold coldQAtRoot
  exact add_nonneg (by exact_mod_cast hc.1)
    (mul_nonneg (by exact_mod_cast hc.2) (by positivity))

theorem cold_graph_bad_nonneg :
    ∀ j ∈ coldUpdatedLags,
      0 ≤ coldGraphContribution j ∧ 0 ≤ coldBadHistory j := by
  decide +kernel

theorem cold_updated_lag_bounds (j : ℕ) (hj : j ∈ coldUpdatedLags) :
    4 ≤ j ∧ j ≤ 128 := by
  change j ∈ (List.range 63).map (fun i => 4 + 2*i) at hj
  rcases List.mem_map.mp hj with ⟨i, hi, rfl⟩
  have hi' : i < 63 := List.mem_range.mp hi
  omega

theorem cold_transport_index_lt (j r : ℕ) (hj : j ∈ coldUpdatedLags)
    (hr : r ∈ coldTransportIndices j) : j-r < j := by
  rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
  have hjb := cold_updated_lag_bounds j hj
  have hi' : i < j/2 := List.mem_range.mp hi
  omega

theorem cold_transport_index_le (j r : ℕ) (hj : j ∈ coldUpdatedLags)
    (hr : r ∈ coldTransportIndices j) : r ≤ j := by
  rcases List.mem_map.mp hj with ⟨k, hk, rfl⟩
  rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
  have hk' : k < 63 := List.mem_range.mp hk
  have hi' : i < (4+2*k)/2 := List.mem_range.mp hi
  omega

theorem cold_initial_mean_values :
    ∀ k ∈ List.range 4, coldMeanAt k = coldA := by
  decide +kernel

theorem cold_even_mem_updated (j : ℕ) (he : Even j)
    (hlo : 4 ≤ j) (hhi : j ≤ 128) : j ∈ coldUpdatedLags := by
  rcases he with ⟨m, hm⟩
  rw [coldUpdatedLags]
  apply List.mem_map.mpr
  refine ⟨m-2, List.mem_range.mpr ?_, ?_⟩
  · omega
  · omega

theorem cold_even_sub_two {j : ℕ} (he : Even j) (hlo : 2 ≤ j) : Even (j-2) := by
  rcases he with ⟨m, hm⟩
  refine ⟨m-1, ?_⟩
  omega

theorem cold_even_sub_of_even {j r : ℕ} (hj : Even j) (hr : Even r)
    (hrj : r ≤ j) : Even (j-r) := by
  rcases hj with ⟨m, hm⟩
  rcases hr with ⟨n, hn⟩
  refine ⟨m-n, ?_⟩
  omega

theorem cold_mean_nonneg_table :
    ∀ k ∈ List.range 129, 0 ≤ coldMeanAt k := by
  decide +kernel

theorem cold_mean_nonneg_real_table :
    ∀ k ∈ List.range 129, 0 ≤ (coldMeanAt k : ℝ) := by
  intro k hk
  exact_mod_cast cold_mean_nonneg_table k hk

/-- The real unrounded recurrence uses the exact `sqrt 3` powers, with the checked rational
history and graph caps as its inputs.  These are precisely the outward cap inputs in
CO-TRIANGULAR-129; only the radical replacement and quotient rounding are removed here. -/
noncomputable def coldExactWeightedMeans (μ : ℕ → ℝ) (j : ℕ) : ℝ :=
  coldRealListSum (coldTransportIndices j)
    (fun r => coldExactQ j r * μ (j-r))

noncomputable def coldExactNumerator (μ : ℕ → ℝ) (j : ℕ) : ℝ :=
  coldExactWeightedMeans μ j + (coldGraphContribution j : ℝ) +
    (coldBadHistory j : ℝ)

noncomputable def coldExactUpdate (μ : ℕ → ℝ) (j : ℕ) : ℝ :=
  min (μ (j-2)) (coldExactNumerator μ j / coldExactDenominator j)

def coldRealListSumAttach {α : Type} (xs : List α)
    (f : {x // x ∈ xs} → ℝ) : ℝ := (xs.attach.map f).sum

theorem coldRealListSum_attach_eq {α : Type} (xs : List α) (f : α → ℝ) :
    coldRealListSumAttach xs (fun x => f x.val) = coldRealListSum xs f := by
  induction xs with
  | nil => simp [coldRealListSumAttach, coldRealListSum]
  | cons a xs ih => simp [coldRealListSumAttach, coldRealListSum]

noncomputable def coldExactMeanStep (n : ℕ) (rec : ∀ m, m < n → ℝ) : ℝ :=
  if h : n ∈ coldUpdatedLags then
    min (rec (n-2) (by have hn := cold_updated_lag_bounds n h; omega))
      ((coldRealListSumAttach (coldTransportIndices n) (fun r =>
          coldExactQ n r.val * rec (n-r.val)
            (cold_transport_index_lt n r.val h r.property)) +
        (coldGraphContribution n : ℝ) + (coldBadHistory n : ℝ)) /
        coldExactDenominator n)
  else (coldMeanAt n : ℝ)

/-- The canonical real-valued sequence with the exact `sqrt 3` recurrence and rational inputs. -/
noncomputable def coldExactMean (n : ℕ) : ℝ :=
  Nat.strongRecOn n coldExactMeanStep

theorem cold_exact_mean_eq_step (n : ℕ) :
    coldExactMean n = coldExactMeanStep n (fun m _ => coldExactMean m) := by
  rw [coldExactMean, Nat.strongRecOn_eq]
  congr 1

theorem cold_exact_mean_initial (n : ℕ) (hn : n < 4) :
    coldExactMean n = (coldMeanAt n : ℝ) := by
  have hnot : n ∉ coldUpdatedLags := by
    intro h
    have hjb := cold_updated_lag_bounds n h
    omega
  rw [cold_exact_mean_eq_step]
  simp [coldExactMeanStep, hnot]

theorem cold_exact_mean_update (j : ℕ) (hj : j ∈ coldUpdatedLags) :
    coldExactMean j = coldExactUpdate coldExactMean j := by
  rw [cold_exact_mean_eq_step]
  simp only [coldExactMeanStep, dite_eq_left hj]
  unfold coldExactUpdate coldExactNumerator coldExactWeightedMeans
  rw [coldRealListSum_attach_eq (coldTransportIndices j)
    (fun r => coldExactQ j r * coldExactMean (j-r))]

theorem cold_exact_adjacent_mono (j : ℕ) (he : Even j)
    (hlo : 2 ≤ j) (hhi : j ≤ 128) :
    coldExactMean j ≤ coldExactMean (j-2) := by
  by_cases hj4 : j < 4
  · rw [cold_exact_mean_initial j (by omega),
      cold_exact_mean_initial (j-2) (by omega)]
    have h₁ := cold_initial_mean_values j (List.mem_range.mpr (by omega))
    have h₂ := cold_initial_mean_values (j-2) (List.mem_range.mpr (by omega))
    rw [h₁, h₂]
  · have hjmem := cold_even_mem_updated j he (by omega) hhi
    rw [cold_exact_mean_update j hjmem]
    exact min_le_left _ _

theorem cold_exact_even_antitone
    {k j : ℕ} (hkj : k ≤ j) (hk : Even k) (hj : Even j) (hbound : j ≤ 128) :
    coldExactMean j ≤ coldExactMean k := by
  rcases hk with ⟨m, hm⟩
  rcases hj with ⟨n, hn⟩
  have hdiff : ∃ d, j = k + 2*d := by
    refine ⟨n-m, ?_⟩
    omega
  rcases hdiff with ⟨d, rfl⟩
  have haux : ∀ d, k + 2*d ≤ 128 →
      coldExactMean (k + 2*d) ≤ coldExactMean k := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        have heven : Even (k + 2*(d+1)) := by
          refine ⟨m + (d+1), ?_⟩
          omega
        have hstep := cold_exact_adjacent_mono (k+2*(d+1)) heven
          (by omega) hd
        have hsub : k + 2*(d+1) - 2 = k + 2*d := by omega
        rw [hsub] at hstep
        exact hstep.trans (ih (by omega))
  exact haux d (by omega)

/-- Upward grid rounding dominates its exact rational input. -/
theorem coldRoundUp_ge (x : ℚ) : x ≤ coldRoundUp x := by
  have hs : 0 < (coldScale : ℚ) := by norm_num [coldScale]
  have hceil := Int.le_ceil ((coldScale : ℚ) * x)
  apply (le_div_iff₀ hs).2
  simpa [coldRoundUp, mul_comm] using hceil

/-- One exact unrounded update is bounded by the rational replay whenever its earlier real means
are below the checked lag caps and are nonincreasing with the lag index. -/
theorem cold_exact_step_le_rational
    (μ : ℕ → ℝ) (j : ℕ) (hj : j ∈ coldUpdatedLags)
    (hprev : μ (j-2) ≤ (coldMeanAt (j-2) : ℝ))
    (hcap : ∀ r ∈ coldTransportIndices j,
      μ (j-r) ≤ (coldMeanAt (j-r) : ℝ))
    (hmono : ∀ r ∈ coldTransportIndices j, μ (j-2) ≤ μ (j-r)) :
    coldExactUpdate μ j ≤ (coldMeanAt j : ℝ) := by
  let xs := coldTransportIndices j
  let p := μ (j-2)
  let dExact := 1 - coldExactFine j
  let dRat := 1 - (coldFineTail j : ℝ)
  let base := (coldGraphContribution j : ℝ) + (coldBadHistory j : ℝ)
  let qExact : ℕ → ℝ := coldExactQ j
  let qRat : ℕ → ℝ := fun r => (coldQ j r : ℝ)
  let xExact : ℕ → ℝ := fun r => μ (j-r)
  let xRat : ℕ → ℝ := fun r => (coldMeanAt (j-r) : ℝ)
  have hcomp : ∀ r ∈ xs, coldExactQ j r ≤ (coldQ j r : ℝ) ∧
      0 ≤ (coldQ j r : ℝ) := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
    have hc := cold_q_components_nonneg j hj i hi
    exact ⟨cold_exact_q_le_rational j (2*(i+1)) hc.2,
      cold_q_nonneg_lags j hj i hi⟩
  have hdenExact : 0 < dExact + coldRealListSum xs qExact := by
    have heq : dExact + coldRealListSum xs qExact = coldExactDenominator j := by
      dsimp [dExact, coldExactDenominator, coldExactFine, coldExactQSum,
        coldExactQ, qExact, xs]
      ring
    rw [heq]
    exact cold_exact_denominator_pos j hj
  have hqStep := cold_min_weighted_ratio_mono p base dExact xs
    qExact qRat xExact hdenExact
    (by intro r hr; exact (hcomp r hr).1)
    (by intro r hr; exact hmono r hr)
  have hqSum : coldRealListSum xs qExact ≤ coldRealListSum xs qRat :=
    coldRealListSum_mono xs qExact qRat (by
      intro r hr
      exact (hcomp r hr).1)
  have hdenRatRad : 0 < dExact + coldRealListSum xs qRat := by
    linarith [hdenExact, hqSum]
  have hmeansStep := cold_min_weighted_means_mono p base dExact xs qRat
    xExact xRat hdenRatRad
    (by intro r hr; exact (hcomp r hr).2)
    (by intro r hr; exact hcap r hr)
  have hmeanNonnegR : ∀ r ∈ xs, 0 ≤ xRat r := by
    intro r hr
    rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
    have hi' : i < j/2 := List.mem_range.mp hi
    have hjb := cold_updated_lag_bounds j hj
    have hk : j - 2*(i+1) < 129 := by omega
    exact cold_mean_nonneg_real_table (j-2*(i+1)) (List.mem_range.mpr hk)
  have hXnonneg : 0 ≤ coldRealListSum xs (fun r => qRat r * xRat r) :=
    coldRealListSum_nonneg xs (fun r => qRat r*xRat r) (by
      intro r hr
      exact mul_nonneg (hcomp r hr).2 (hmeanNonnegR r hr))
  have hbaseNonneg : 0 ≤ base := by
    have hb := cold_graph_bad_nonneg j hj
    have hg : (0 : ℝ) ≤ (coldGraphContribution j : ℝ) := by exact_mod_cast hb.1
    have hbad : (0 : ℝ) ≤ (coldBadHistory j : ℝ) := by exact_mod_cast hb.2
    dsimp [base]
    exact add_nonneg hg hbad
  have hdenRational : 0 < (coldDenominator j : ℝ) := by
    exact_mod_cast (cold_lags_kernel_replay j hj).1
  have hsumRatCast : coldRealListSum xs qRat = (coldQSum j : ℝ) := by
    have h := coldRealListSum_cast xs (coldQ j)
    simpa [qRat, xs, coldTransportIndices, coldQSum] using h
  have hdenCast : dRat + coldRealListSum xs qRat =
      (coldDenominator j : ℝ) := by
    rw [hsumRatCast]
    simp only [coldDenominator]
    push_cast
    ring
  have hdenRatTotal : 0 < dRat + coldRealListSum xs qRat := by
    rw [hdenCast]
    exact hdenRational
  have hdenOrder : dRat + coldRealListSum xs qRat ≤
      dExact + coldRealListSum xs qRat := by
    have hF := cold_exact_fine_le_rational j hj
    dsimp [dRat, dExact]
    linarith
  have hfineStep := cold_min_ratio_base_mono p base base
    (dExact + coldRealListSum xs qRat) (dRat + coldRealListSum xs qRat)
    (coldRealListSum xs (fun r => qRat r*xRat r))
    (coldRealListSum xs (fun r => qRat r*xRat r))
    hdenRatTotal hdenOrder hbaseNonneg le_rfl hXnonneg le_rfl
  have hweightedCast : coldRealListSum xs (fun r => qRat r*xRat r) =
      (coldWeightedMeans j : ℝ) := by
    have h := coldRealListSum_cast xs
      (fun r => coldQ j r * coldMeanAt (j-r))
    simpa [qRat, xRat, xs, coldTransportIndices, coldWeightedMeans] using h
  have hnumCast : base + coldRealListSum xs (fun r => qRat r*xRat r) =
      (coldNumerator j : ℝ) := by
    rw [hweightedCast]
    dsimp [base]
    unfold coldNumerator
    push_cast
    ring
  have hratioCast :
      (base + coldRealListSum xs (fun r => qRat r*xRat r)) /
        (dRat + coldRealListSum xs qRat) =
      ((coldNumerator j / coldDenominator j : ℚ) : ℝ) := by
    rw [hnumCast, hdenCast]
    norm_cast
  have hquotRound : (coldNumerator j / coldDenominator j : ℚ) ≤
      coldRoundUp (coldNumerator j / coldDenominator j) :=
    coldRoundUp_ge _
  have hquotRoundR :
      ((coldNumerator j / coldDenominator j : ℚ) : ℝ) ≤
        (coldRoundUp (coldNumerator j / coldDenominator j) : ℝ) := by
    exact_mod_cast hquotRound
  have hcapRound : min (coldMeanAt (j-2) : ℝ)
      ((coldNumerator j / coldDenominator j : ℚ) : ℝ) ≤
      (coldUpdate j : ℝ) := by
    have h := min_le_min (le_refl (coldMeanAt (j-2) : ℝ)) hquotRoundR
    simpa [coldUpdate] using h
  have hprev' : p ≤ (coldMeanAt (j-2) : ℝ) := hprev
  have hprevStep : min p ((coldNumerator j / coldDenominator j : ℚ) : ℝ) ≤
      min (coldMeanAt (j-2) : ℝ)
        ((coldNumerator j / coldDenominator j : ℚ) : ℝ) :=
    min_le_min hprev' (le_refl ((coldNumerator j / coldDenominator j : ℚ) : ℝ))
  have hlast : min p
      ((base + coldRealListSum xs (fun r => qRat r*xRat r)) /
        (dRat + coldRealListSum xs qRat)) ≤
      min (coldMeanAt (j-2) : ℝ)
        ((coldNumerator j / coldDenominator j : ℚ) : ℝ) := by
    rw [hratioCast]
    exact hprevStep
  have hfinal : min p
      ((base + coldRealListSum xs (fun r => qExact r*xExact r)) /
        (dExact + coldRealListSum xs qExact)) ≤
      min (coldMeanAt (j-2) : ℝ)
        ((coldNumerator j / coldDenominator j : ℚ) : ℝ) :=
    hqStep.trans (hmeansStep.trans (hfineStep.trans hlast))
  have hchain : coldExactUpdate μ j ≤
      min (coldMeanAt (j-2) : ℝ)
        ((coldNumerator j / coldDenominator j : ℚ) : ℝ) := by
    calc
      coldExactUpdate μ j = min p
          ((base + coldRealListSum xs (fun r => qExact r*xExact r)) /
            (dExact + coldRealListSum xs qExact)) := by
        unfold coldExactUpdate coldExactNumerator coldExactWeightedMeans
          coldExactDenominator coldExactQSum
        dsimp [p, dExact, base, qExact, xExact, xs]
        congr 2 <;> ring
      _ ≤ _ := hfinal
  have hupdate := hchain.trans hcapRound
  rw [(cold_lags_kernel_replay j hj).2]
  exact hupdate

/-- Every even exact mean through lag 128 is dominated by the checked outward table.
The exact recurrence itself supplies the monotone-lag input: its outer minimum gives the
adjacent decrease, and the transport indices are all even. -/
theorem cold_exact_mean_dominates :
    ∀ j ≤ 128, Even j → coldExactMean j ≤ (coldMeanAt j : ℝ) := by
  intro j hj he
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hsmall : j < 4
      · rw [cold_exact_mean_initial j hsmall]
      · have hjmem := cold_even_mem_updated j he (by omega) hj
        have hprev : coldExactMean (j-2) ≤ (coldMeanAt (j-2) : ℝ) :=
          ih (j-2) (by omega) (by omega) (cold_even_sub_two he (by omega))
        have hcap : ∀ r ∈ coldTransportIndices j,
            coldExactMean (j-r) ≤ (coldMeanAt (j-r) : ℝ) := by
          intro r hr
          rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
          have hrEven : Even (2*(i+1)) := by
            refine ⟨i+1, ?_⟩
            omega
          have hlagEven : Even (j-2*(i+1)) :=
            cold_even_sub_of_even he hrEven
              (cold_transport_index_le j (2*(i+1)) hjmem
                (List.mem_map.mpr ⟨i, hi, rfl⟩))
          have hlt := cold_transport_index_lt j (2*(i+1)) hjmem
            (List.mem_map.mpr ⟨i, hi, rfl⟩)
          exact ih (j-2*(i+1)) hlt (by omega) hlagEven
        have hmono : ∀ r ∈ coldTransportIndices j,
            coldExactMean (j-2) ≤ coldExactMean (j-r) := by
          intro r hr
          rcases List.mem_map.mp hr with ⟨i, hi, rfl⟩
          have hrEven : Even (2*(i+1)) := by
            refine ⟨i+1, ?_⟩
            omega
          have hlagEven : Even (j-2*(i+1)) :=
            cold_even_sub_of_even he hrEven
              (cold_transport_index_le j (2*(i+1)) hjmem
                (List.mem_map.mpr ⟨i, hi, rfl⟩))
          have hprevEven : Even (j-2) := cold_even_sub_two he (by omega)
          have horder : j-2*(i+1) ≤ j-2 := by omega
          exact cold_exact_even_antitone horder hlagEven hprevEven (by omega)
        rw [cold_exact_mean_update j hjmem]
        exact cold_exact_step_le_rational coldExactMean j hjmem hprev hcap hmono

end ASDExplicitGamma.Numerics.Cold
