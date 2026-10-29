module

public import ASDExplicitGamma.Triadic.SensitivityQuadratic
public import ASDExplicitGamma.Triadic.TriadicDualNorms

/-! Algebra of the weak Haar energy needed for polarized sensitivity. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

private theorem sensitivity_pairing_neg_right (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q f (-g) = -pairing Q f g := by
  have hzero : MemLp (fun _ : Vec 2 => (0 : ℝ)) 2 (normalizedCubeMeasure Q) := by
    exact memLp_const 0
  have h := pairing_sub_right Q hf hzero hg
  simpa [pairing, cubeAverage_const] using h

private theorem sensitivity_energy_add (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x + g x) =
      energy Q f + 2 * pairing Q f g + energy Q g := by
  have hneg : energy Q (-g) = energy Q g := by
    unfold energy pairing
    congr 1
    funext x
    simp only [Pi.neg_apply]
    ring
  have hsub := energy_sub Q hf hg.neg
  have hfun : (fun x => f x + g x) = (fun x => f x - (-g x)) := by
    funext x
    ring
  calc
    energy Q (fun x => f x + g x) = energy Q (fun x => f x - (-g x)) := by
      exact congrArg (energy Q) hfun
    _ = energy Q f - 2 * pairing Q f (-g) + energy Q (-g) := by
      exact hsub
    _ = energy Q f + 2 * pairing Q f g + energy Q g := by
      rw [sensitivity_pairing_neg_right Q hf hg, hneg]
      ring

private theorem sensitivity_energy_smul (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (c : ℝ) :
    energy Q (fun x => c * f x) = c ^ 2 * energy Q f := by
  rw [energy_eq_integral_sq, energy_eq_integral_sq]
  simp only [mul_pow]
  rw [integral_const_mul]

private theorem sensitivity_cubeIncrement_smul (Q : TriadicCube 2) (n : ℕ)
    (f : Vec 2 → ℝ) (c : ℝ) :
    cubeIncrement Q n (fun x => c * f x) =
      fun x => c * cubeIncrement Q n f x := by
  cases n with
  | zero => simp [cubeIncrement_zero, projection_smul]
  | succ n =>
      simp only [cubeIncrement_succ, projection_smul]
      funext x
      ring

/-- Positive Haar energy is quadratic under scalar multiplication. -/
theorem sensitivity_primalEnergy_smul (Q : TriadicCube 2) (q : ℝ)
    (f : Vec 2 → ℝ) (c : ℝ) :
    primalEnergy Q q (fun x => c * f x) = c ^ 2 * primalEnergy Q q f := by
  unfold primalEnergy
  rw [sensitivity_cubeIncrement_smul, sensitivity_energy_smul]
  have hterm (n : ℕ) :
      q ^ (n + 1) * energy Q (cubeIncrement Q (n + 1) (fun x => c * f x)) =
        c ^ 2 * (q ^ (n + 1) * energy Q (cubeIncrement Q (n + 1) f)) := by
    rw [sensitivity_cubeIncrement_smul, sensitivity_energy_smul]
    ring
  rw [show (∑' n, q ^ (n + 1) *
      energy Q (cubeIncrement Q (n + 1) (fun x => c * f x))) =
      ∑' n, c ^ 2 * (q ^ (n + 1) * energy Q (cubeIncrement Q (n + 1) f)) by
        exact tsum_congr hterm, tsum_mul_left]
  ring

/-- The squared positive Haar norm has the same quadratic scaling. -/
theorem sensitivity_positiveHaarNorm_smul_sq (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (c : ℝ) :
    positiveHaarNorm Q (fun x => c * f x) ^ 2 =
      c ^ 2 * positiveHaarNorm Q f ^ 2 := by
  rw [positiveHaarNorm, positiveHaarNorm]
  rw [Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3)
      (Real.sqrt_nonneg 3) (fun x => c * f x)),
    Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3)
      (Real.sqrt_nonneg 3) f)]
  exact sensitivity_primalEnergy_smul Q (Real.sqrt 3) f c

/-- Adding a constant mode to a mean-zero field adds exactly its squared
constant to the weak Haar energy. -/
theorem sensitivity_dualEnergy_add_const_meanZero (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hmean : cubeAverage Q f = 0) (c : ℝ) :
    dualEnergy Q (Real.sqrt 3) (fun x => f x + c) =
      dualEnergy Q (Real.sqrt 3) f + c ^ 2 := by
  let w : ℝ := Real.sqrt 3
  let ρ : ℝ := w⁻¹
  let d : ℝ := 1 - ρ
  have hw : 1 < w := by
    dsimp [w]
    nlinarith [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    exact (inv_lt_one₀ (show (0 : ℝ) < w by positivity)).2 hw
  have hd : 0 < d := by dsimp [d]; linarith
  have hfc : MemLp (fun x => f x + c) 2 (normalizedCubeMeasure Q) :=
    hf.add (memLp_const c)
  have hconst (n : ℕ) {x : Vec 2} (hx : x ∈ cubeSet Q) :
      cubeProjection Q n (fun _ : Vec 2 => c) x = c := by
    obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet n hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
    exact cubeAverage_const R c
  have hprojMean (n : ℕ) : cubeAverage Q (cubeProjection Q n f) = 0 := by
    rw [cubeAverage_cubeProjection_eq_cubeAverage_of_memLp Q n f hf]
    exact hmean
  have hcross (n : ℕ) :
      pairing Q (cubeProjection Q n f) (cubeProjection Q n (fun _ : Vec 2 => c)) = 0 := by
    unfold pairing
    have hprod : ∀ x ∈ cubeSet Q,
        cubeProjection Q n f x * cubeProjection Q n (fun _ : Vec 2 => c) x =
          c * cubeProjection Q n f x := by
      intro x hx
      rw [hconst n hx]
      ring
    rw [cubeAverage_congr_on_cubeSet hprod,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    have hmeanInt :
        (∫ x, cubeProjection Q n f x ∂normalizedCubeMeasure Q) = 0 := by
      rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
      exact hprojMean n
    calc
      (∫ x, c * cubeProjection Q n f x ∂normalizedCubeMeasure Q) =
          c * ∫ x, cubeProjection Q n f x ∂normalizedCubeMeasure Q :=
        integral_const_mul c _
      _ = 0 := by rw [hmeanInt]; ring
  have hconstEnergy (n : ℕ) :
      energy Q (cubeProjection Q n (fun _ : Vec 2 => c)) = c ^ 2 := by
    unfold energy pairing
    have hsq : ∀ x ∈ cubeSet Q,
        cubeProjection Q n (fun _ : Vec 2 => c) x *
            cubeProjection Q n (fun _ : Vec 2 => c) x = c ^ 2 := by
      intro x hx
      rw [hconst n hx]
      ring
    rw [cubeAverage_congr_on_cubeSet hsq, cubeAverage_const]
  have hprojAdd (n : ℕ) :
      cubeProjection Q n (fun x => f x + c) =
        fun x => cubeProjection Q n f x + cubeProjection Q n (fun _ : Vec 2 => c) x := by
    exact projection_add Q n hf (memLp_const c)
  have henergy (n : ℕ) :
      energy Q (cubeProjection Q n (fun x => f x + c)) =
        energy Q (cubeProjection Q n f) + c ^ 2 := by
    rw [hprojAdd, sensitivity_energy_add Q (projection_memLp Q n f 2)
      (projection_memLp Q n (fun _ : Vec 2 => c) 2), hcross, hconstEnergy]
    ring
  have hsF := summable_weighted_projections Q hw hf
  have hsC : Summable (fun n : ℕ => ρ ^ n * c ^ 2) := by
    simpa [ρ, mul_comm] using
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left (c ^ 2)
  have hgeom := tsum_geometric_of_lt_one hρ0 hρ1
  have hsum :
      (∑' n, ρ ^ n * energy Q (cubeProjection Q n (fun x => f x + c))) =
        (∑' n, ρ ^ n * energy Q (cubeProjection Q n f)) +
          c ^ 2 * (∑' n, ρ ^ n) := by
    calc
      _ = ∑' n, (ρ ^ n * energy Q (cubeProjection Q n f) + ρ ^ n * c ^ 2) :=
        tsum_congr fun n => by rw [henergy n]; ring
      _ = (∑' n, ρ ^ n * energy Q (cubeProjection Q n f)) +
          ∑' n, ρ ^ n * c ^ 2 := hsF.tsum_add hsC
      _ = _ := by
        congr 1
        calc
          (∑' n, ρ ^ n * c ^ 2) = ∑' n, c ^ 2 * ρ ^ n :=
            tsum_congr fun n => by ring
          _ = c ^ 2 * (∑' n, ρ ^ n) := tsum_mul_left
  rw [dualEnergy_eq Q hw hfc, dualEnergy_eq Q hw hf]
  change d * (∑' n, ρ ^ n * energy Q (cubeProjection Q n (fun x => f x + c))) =
    d * (∑' n, ρ ^ n * energy Q (cubeProjection Q n f)) + c ^ 2
  rw [hsum, hgeom]
  dsimp [d]
  have hden : 1 - ρ ≠ 0 := by
    change d ≠ 0
    exact ne_of_gt hd
  field_simp [hden]

/-- The vector weak energy separates a constant mode from a mean-zero field
coordinate by coordinate. -/
theorem sensitivity_vectorWeakEnergy_sub_const_meanZero (Q : TriadicCube 2)
    (F : Vec 2 → Fin 2 → ℝ) (p : Vec 2)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hmean : ∀ i, cubeAverage Q (fun x => F x i) = 0) :
    vectorWeakHaarEnergy Q (fun x i => F x i - p i) =
      vectorWeakHaarEnergy Q F + ∑ i, (p i) ^ 2 := by
  unfold vectorWeakHaarEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h := sensitivity_dualEnergy_add_const_meanZero Q (hF i) (hmean i) (-p i)
  simpa [sub_eq_add_neg] using h

/-- The negative-weight Haar energy is quadratic, with the exact parallelogram
identity on the dyadic projection coefficients. -/
theorem sensitivity_dualEnergy_parallelogram (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q (Real.sqrt 3) (fun x => f x + g x) +
        dualEnergy Q (Real.sqrt 3) (fun x => f x - g x) =
      2 * dualEnergy Q (Real.sqrt 3) f + 2 * dualEnergy Q (Real.sqrt 3) g := by
  let w : ℝ := Real.sqrt 3
  have hw : 1 < w := by
    dsimp [w]
    nlinarith [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hneg : MemLp (fun x => -g x) 2 (normalizedCubeMeasure Q) := hg.neg
  have hplus : MemLp (fun x => f x + g x) 2 (normalizedCubeMeasure Q) := hf.add hg
  have hminus : MemLp (fun x => f x - g x) 2 (normalizedCubeMeasure Q) := hf.sub hg
  have hsp := summable_weighted_projections Q hw hplus
  have hsm := summable_weighted_projections Q hw hminus
  have hsf := summable_weighted_projections Q hw hf
  have hsg := summable_weighted_projections Q hw hg
  have hterm (n : ℕ) :
      w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x + g x)) +
        w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x - g x)) =
      2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n f)) +
        2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n g)) := by
    have hprojP := projection_add Q n hf hg
    have hprojNeg : cubeProjection Q n (fun x => -g x) =
        fun x => -cubeProjection Q n g x := by
      have h := projection_smul Q n g (-1)
      simpa using h
    have hprojM : cubeProjection Q n (fun x => f x - g x) =
        fun x => cubeProjection Q n f x - cubeProjection Q n g x := by
      simpa only [sub_eq_add_neg, hprojNeg] using projection_add Q n hf hneg
    have hEp := sensitivity_energy_add Q
      (projection_memLp Q n f 2) (projection_memLp Q n g 2)
    have hEm := energy_sub Q (projection_memLp Q n f 2) (projection_memLp Q n g 2)
    have hplusEnergy : energy Q (cubeProjection Q n (fun x => f x + g x)) =
        energy Q (cubeProjection Q n f) +
          2 * pairing Q (cubeProjection Q n f) (cubeProjection Q n g) +
          energy Q (cubeProjection Q n g) := by
      rw [hprojP]
      exact hEp
    have hminusEnergy : energy Q (cubeProjection Q n (fun x => f x - g x)) =
        energy Q (cubeProjection Q n f) -
          2 * pairing Q (cubeProjection Q n f) (cubeProjection Q n g) +
          energy Q (cubeProjection Q n g) := by
      rw [hprojM]
      exact hEm
    rw [hplusEnergy, hminusEnergy]
    ring
  have htsum :
      (∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x + g x))) +
        ∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x - g x)) =
      2 * (∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n f)) +
        2 * (∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n g)) := by
    calc
      _ = ∑' n, (w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x + g x)) +
          w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x - g x))) :=
        (hsp.tsum_add hsm).symm
      _ = ∑' n, (2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n f)) +
          2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n g))) := tsum_congr hterm
      _ = _ := by
        calc
          _ = (∑' n, 2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n f))) +
              ∑' n, 2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n g)) :=
            (hsf.mul_left 2).tsum_add (hsg.mul_left 2)
          _ = _ := by rw [tsum_mul_left, tsum_mul_left]
  rw [dualEnergy_eq Q hw hplus, dualEnergy_eq Q hw hminus,
    dualEnergy_eq Q hw hf, dualEnergy_eq Q hw hg]
  calc
    (1 - w⁻¹) * ∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x + g x)) +
        (1 - w⁻¹) * ∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x - g x)) =
      (1 - w⁻¹) *
        ((∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x + g x))) +
          ∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => f x - g x))) := by ring
    _ = 2 * ((1 - w⁻¹) * ∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n f)) +
        2 * ((1 - w⁻¹) * ∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n g)) := by rw [htsum]; ring

/-- Multiplication by a scalar scales the weak Haar energy quadratically. -/
theorem sensitivity_dualEnergy_smul (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    dualEnergy Q (Real.sqrt 3) (fun x => c * f x) =
      c ^ 2 * dualEnergy Q (Real.sqrt 3) f := by
  let w : ℝ := Real.sqrt 3
  have hw : 1 < w := by
    dsimp [w]
    nlinarith [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have hc : MemLp (fun x => c * f x) 2 (normalizedCubeMeasure Q) := hf.const_mul c
  have hs := summable_weighted_projections Q hw hf
  have hterm (n : ℕ) :
      w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => c * f x)) =
      c ^ 2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n f)) := by
    rw [projection_smul, sensitivity_energy_smul]
    ring
  have htsum :
      (∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n (fun x => c * f x))) =
        c ^ 2 * (∑' n, w⁻¹ ^ n * energy Q (cubeProjection Q n f)) := by
    calc
      _ = ∑' n, c ^ 2 * (w⁻¹ ^ n * energy Q (cubeProjection Q n f)) := tsum_congr hterm
      _ = _ := tsum_mul_left
  rw [dualEnergy_eq Q hw hc, dualEnergy_eq Q hw hf]
  rw [htsum]
  ring

/-- The vector weak energy is the sum of its coordinate parallelogram laws. -/
theorem sensitivity_vectorWeakEnergy_parallelogram (Q : TriadicCube 2)
    (F G : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarEnergy Q (fun x i => F x i + G x i) +
        vectorWeakHaarEnergy Q (fun x i => F x i - G x i) =
      2 * vectorWeakHaarEnergy Q F + 2 * vectorWeakHaarEnergy Q G := by
  unfold vectorWeakHaarEnergy
  calc
    _ = ∑ i, (dualEnergy Q (Real.sqrt 3) (fun x => F x i + G x i) +
        dualEnergy Q (Real.sqrt 3) (fun x => F x i - G x i)) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ i, (2 * dualEnergy Q (Real.sqrt 3) (fun x => F x i) +
        2 * dualEnergy Q (Real.sqrt 3) (fun x => G x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sensitivity_dualEnergy_parallelogram Q (hF i) (hG i)
    _ = 2 * ∑ i, dualEnergy Q (Real.sqrt 3) (fun x => F x i) +
        2 * ∑ i, dualEnergy Q (Real.sqrt 3) (fun x => G x i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Coordinatewise scalar multiplication has the expected quadratic energy. -/
theorem sensitivity_vectorWeakEnergy_smul (Q : TriadicCube 2)
    (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    vectorWeakHaarEnergy Q (fun x i => c * F x i) =
      c ^ 2 * vectorWeakHaarEnergy Q F := by
  unfold vectorWeakHaarEnergy
  calc
    _ = ∑ i, (c ^ 2 * dualEnergy Q (Real.sqrt 3) (fun x => F x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sensitivity_dualEnergy_smul Q (hF i) c
    _ = c ^ 2 * ∑ i, dualEnergy Q (Real.sqrt 3) (fun x => F x i) := by
      rw [Finset.mul_sum]

end

end ASDExplicitGamma.Triadic
