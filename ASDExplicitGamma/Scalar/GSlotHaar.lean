module

public import ASDExplicitGamma.Scalar.FlatSourceHaarLimit
public import ASDExplicitGamma.Triadic.HaarParseval

/-! Orthogonality, self-adjointness and polar Parseval for the scalar Haar increments of a cube,
at the level of the normalized `L²` pairing and of the contraction `cubeIncrementL2CLM`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic
open scoped BigOperators Topology InnerProductSpace

section Function

variable (R : TriadicCube 2)

theorem pairing_congr_ae {f f' g g' : Vec 2 → ℝ}
    (hf : f =ᵐ[normalizedCubeMeasure R] f') (hg : g =ᵐ[normalizedCubeMeasure R] g') :
    pairing R f g = pairing R f' g' := by
  unfold pairing
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_congr_ae (hf.mul hg)

theorem pairing_zero_left (g : Vec 2 → ℝ) : pairing R (fun _ => (0 : ℝ)) g = 0 := by
  simp [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]

theorem projection_sub {f g : Vec 2 → ℝ} (k : ℕ)
    (hf : MemLp f 2 (normalizedCubeMeasure R)) (hg : MemLp g 2 (normalizedCubeMeasure R)) :
    cubeProjection R k (fun x => f x - g x) =
      fun x => cubeProjection R k f x - cubeProjection R k g x := by
  have h : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by funext x; ring
  rw [h, projection_add R k hf (hg.const_mul (-1)), projection_smul R k g (-1)]
  funext x; ring

theorem projection_increment {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure R))
    (a k : ℕ) :
    cubeProjection R a (cubeIncrement R k f) =
      if k ≤ a then cubeIncrement R k f else fun _ => 0 := by
  cases k with
  | zero =>
    simp only [cubeIncrement_zero, Nat.zero_le, ↓reduceIte]
    exact projection_projection_of_ge R (Nat.zero_le a) f
  | succ k =>
    have hinc : cubeIncrement R (k + 1) f =
        fun x => cubeProjection R (k + 1) f x - cubeProjection R k f x := by
      funext x; simp only [cubeIncrement_succ]
    rw [hinc, projection_sub R a (projection_memLp R (k + 1) f 2) (projection_memLp R k f 2),
      projection_projection R a (k + 1) hf, projection_projection R a k hf]
    by_cases h : k + 1 ≤ a
    · simp only [h, ↓reduceIte]; rw [min_eq_right h, min_eq_right (Nat.le_of_succ_le h)]
    · simp only [h, ↓reduceIte]; rw [min_eq_left (not_le.mp h).le, min_eq_left (Nat.lt_succ_iff.mp (not_le.mp h))]
      funext x; simp

theorem pairing_increment_increment {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure R)) (hg : MemLp g 2 (normalizedCubeMeasure R))
    (j k : ℕ) :
    pairing R (cubeIncrement R j f) (cubeIncrement R k g) =
      if j = k then pairing R (cubeIncrement R k f) g else 0 := by
  have hj := increment_memLp R j f
  have hP (a : ℕ) : pairing R (cubeIncrement R j f) (cubeProjection R a g) =
      if j ≤ a then pairing R (cubeIncrement R j f) g else 0 := by
    rw [← projection_selfAdjoint R a hj hg, projection_increment R hf a j]
    split_ifs
    · rfl
    · exact pairing_zero_left R g
  cases k with
  | zero =>
    simp only [cubeIncrement_zero]
    rw [hP 0]
    by_cases h : j = 0
    · subst h; simp
    · have : ¬ j ≤ 0 := fun h' => h (Nat.le_zero.mp h')
      simp [h, this]
  | succ k =>
    have hinc : cubeIncrement R (k + 1) g =
        fun x => cubeProjection R (k + 1) g x - cubeProjection R k g x := by
      funext x; simp only [cubeIncrement_succ]
    rw [hinc, pairing_sub_right R hj (projection_memLp R (k + 1) g 2) (projection_memLp R k g 2),
      hP, hP]
    by_cases h1 : j ≤ k
    · have h2 : j ≤ k + 1 := Nat.le_succ_of_le h1
      have h3 : j ≠ k + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : j = k + 1
      · subst h2; simp
      · have h3 : ¬ j ≤ k + 1 := by omega
        simp [h1, h2, h3]

theorem pairing_increment_selfAdjoint {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure R)) (hg : MemLp g 2 (normalizedCubeMeasure R))
    (k : ℕ) :
    pairing R (cubeIncrement R k f) g = pairing R f (cubeIncrement R k g) := by
  cases k with
  | zero => simpa only [cubeIncrement_zero] using projection_selfAdjoint R 0 hf hg
  | succ k =>
    have hinc (u : Vec 2 → ℝ) : cubeIncrement R (k + 1) u =
        fun x => cubeProjection R (k + 1) u x - cubeProjection R k u x := by
      funext x; simp only [cubeIncrement_succ]
    rw [hinc f, hinc g, pairing_sub_left R (projection_memLp R (k + 1) f 2)
      (projection_memLp R k f 2) hg, pairing_sub_right R hf (projection_memLp R (k + 1) g 2)
      (projection_memLp R k g 2), projection_selfAdjoint R (k + 1) hf hg,
      projection_selfAdjoint R k hf hg]

end Function

section Lp

variable (R : TriadicCube 2)

theorem inner_lp (f g : Lp ℝ 2 (normalizedCubeMeasure R)) :
    ⟪f, g⟫_ℝ = pairing R (fun x => f x) (fun x => g x) := by
  rw [MeasureTheory.L2.inner_def]
  simp only [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem inc_coe (k : ℕ) (f : Lp ℝ 2 (normalizedCubeMeasure R)) :
    (fun x => cubeIncrementL2CLM R k f x) =ᵐ[normalizedCubeMeasure R]
      cubeIncrement R k (fun x => f x) := by
  rw [cubeIncrementL2CLM_apply, cubeIncrementToLp]
  exact (increment_memLp R k (fun x => f x)).coeFn_toLp

theorem inner_inc_inc (j k : ℕ) (f g : Lp ℝ 2 (normalizedCubeMeasure R)) :
    ⟪cubeIncrementL2CLM R j f, cubeIncrementL2CLM R k g⟫_ℝ =
      if j = k then ⟪cubeIncrementL2CLM R k f, g⟫_ℝ else 0 := by
  rw [inner_lp, pairing_congr_ae R (inc_coe R j f) (inc_coe R k g),
    pairing_increment_increment R (Lp.memLp f) (Lp.memLp g)]
  split_ifs
  · rw [inner_lp, pairing_congr_ae R (inc_coe R k f) (Filter.EventuallyEq.refl _ _)]
  · rfl

theorem inner_inc_left (k : ℕ) (f g : Lp ℝ 2 (normalizedCubeMeasure R)) :
    ⟪cubeIncrementL2CLM R k f, g⟫_ℝ = ⟪f, cubeIncrementL2CLM R k g⟫_ℝ := by
  rw [inner_lp, inner_lp, pairing_congr_ae R (inc_coe R k f)
    (Filter.EventuallyEq.refl _ _), pairing_congr_ae R (Filter.EventuallyEq.refl _ _)
    (inc_coe R k g)]
  exact pairing_increment_selfAdjoint R (Lp.memLp f) (Lp.memLp g) k

theorem pairing_projection_tendsto {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure R)) (hg : MemLp g 2 (normalizedCubeMeasure R)) :
    Tendsto (fun N => pairing R (cubeProjection R N f) (cubeProjection R N g)) atTop
      (𝓝 (pairing R f g)) := by
  have hconj : Homogenization.cubeBesovConjExponent (2 : ENNReal) = 2 := by
    simpa [Homogenization.cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ENNReal)) (q := (2 : ENNReal)))
  have hconjTop : Homogenization.cubeBesovConjExponent (2 : ENNReal) ≠ (⊤ : ENNReal) := by
    rw [hconj]; norm_num
  have hconv := Homogenization.tendsto_cubeBesovPairing_projection_left_of_memLp
    R (2 : ENNReal) f g hf (by simpa only [hconj] using hg) (by norm_num) (by norm_num) hconjTop
  have hpairconv : Tendsto (fun n => pairing R (cubeProjection R (n + 1) f)
      (cubeProjection R (n + 1) g)) atTop (𝓝 (pairing R f g)) := by
    have hconv' : Tendsto (fun n => pairing R (cubeProjection R (n + 1) f) g) atTop
        (𝓝 (pairing R f g)) := by
      simpa only [Homogenization.cubeBesovPairing, pairing] using hconv
    have heq : ∀ n, pairing R (cubeProjection R (n + 1) f) (cubeProjection R (n + 1) g) =
        pairing R (cubeProjection R (n + 1) f) g := by
      intro n
      calc pairing R (cubeProjection R (n + 1) f) (cubeProjection R (n + 1) g) =
          pairing R f (cubeProjection R (n + 1) g) := by
            simpa only [Nat.min_self] using (pairing_projections R (n + 1) (n + 1) hf hg)
        _ = pairing R (cubeProjection R (n + 1) f) g :=
            (projection_selfAdjoint R (n + 1) hf hg).symm
        _ = _ := rfl
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n => (heq n).symm) hconv'
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 hpairconv

/-- **Polar Parseval** for the Haar increments of a cube. -/
theorem inner_hasSum (f g : Lp ℝ 2 (normalizedCubeMeasure R)) :
    HasSum (fun k => ⟪cubeIncrementL2CLM R k f, cubeIncrementL2CLM R k g⟫_ℝ)
      ⟪f, g⟫_ℝ := by
  have hsq : ∀ h : Lp ℝ 2 (normalizedCubeMeasure R), Summable
      (fun k => ‖cubeIncrementL2CLM R k h‖ ^ 2) := by
    intro h
    have := summable_cubeIncrement_energy R (Lp.memLp h)
    simpa only [energy_cubeIncrement_eq_clm_norm_sq] using this
  have hs : Summable (fun k => ⟪cubeIncrementL2CLM R k f, cubeIncrementL2CLM R k g⟫_ℝ) := by
    refine Summable.of_norm_bounded (((hsq f).add (hsq g))) (fun k => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖cubeIncrementL2CLM R k f‖ - ‖cubeIncrementL2CLM R k g‖),
      norm_nonneg (cubeIncrementL2CLM R k f), norm_nonneg (cubeIncrementL2CLM R k g)]
  have h1 := (hs.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have h2 := pairing_projection_tendsto R (Lp.memLp f) (Lp.memLp g)
  have heq : ∀ N, ∑ k ∈ Finset.range (N + 1),
      ⟪cubeIncrementL2CLM R k f, cubeIncrementL2CLM R k g⟫_ℝ =
      pairing R (cubeProjection R N (fun x => f x)) (cubeProjection R N (fun x => g x)) := by
    intro N
    rw [pairing_projection_sum R N (Lp.memLp f) (Lp.memLp g)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_lp, pairing_congr_ae R (inc_coe R k f) (inc_coe R k g)]
  have h3 : Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      ⟪cubeIncrementL2CLM R k f, cubeIncrementL2CLM R k g⟫_ℝ) atTop
      (𝓝 ⟪f, g⟫_ℝ) := by
    simp only [heq]
    rw [inner_lp]
    exact h2
  have := tendsto_nhds_unique h1 h3
  rw [← this]
  exact hs.hasSum

end Lp

end ASDExplicitGamma.Scalar
