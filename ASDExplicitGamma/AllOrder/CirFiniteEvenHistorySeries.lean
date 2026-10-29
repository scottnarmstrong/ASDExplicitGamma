/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorHistory
public import ASDExplicitGamma.Variational.LemmaVH1

/-! # Spatially uniform envelope for the complete CIR inverse history -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
  ASDExplicitGamma.Inverse ASDExplicitGamma.Variational

namespace ASDExplicitGamma.AllOrder

noncomputable section

/-- The source discount for the complete inverse history. -/
noncomputable def aoCirInverseHistoryDiscount : ℝ :=
  Real.rpow 3 (-(1 / 4 : ℝ))

private theorem aoCir_inverseDepth_nested_bound
    (Q R : TriadicCube 2) (j k : ℕ) {a : CoeffField 2}
    (hR : R ∈ descendantsAtDepth Q j) :
    lemmaVInverseDepthMax R a k ≤ lemmaVInverseDepthMax Q a (j + k) := by
  classical
  unfold lemmaVInverseDepthMax
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty R k)
  intro S hS
  unfold Book.Ch02.finsetSupReal
  exact le_csSup (((Set.toFinite _).image _).bddAbove)
    ⟨S, mem_descendantsAtDepth_add hR hS, rfl⟩

private theorem aoCir_tile_inverseHistory_le_parent_depth_series
    (Q R : TriadicCube 2) (a : CoeffField 2) (j : ℕ) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    lemmaVInverseHistory R a (Real.rpow 3 (1 / 4 : ℝ)) ≤
      (1 - aoCirInverseHistoryDiscount) *
        ∑' d : ℕ, aoCirInverseHistoryDiscount ^ d *
          lemmaVInverseDepthMax Q a (j + d) := by
  let q₀ : ℝ := Real.rpow 3 (1 / 4 : ℝ)
  let α : ℝ := aoCirInverseHistoryDiscount
  let r : ℝ := q₀⁻¹
  have hq₀ : 1 < q₀ := by
    dsimp [q₀]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hα : r = α := by
    dsimp [r, q₀, α, aoCirInverseHistoryDiscount]
    exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) _).symm
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq₀)).2 hq₀
  have hcoef : 0 ≤ 1 - r := by linarith
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hsQ : Summable (fun d : ℕ => r ^ d * lemmaVInverseDepthMax Q a d) := by
    simpa only [r, q₀] using lemmaVInverseHistory_summable Q hEll hq₀
  have htail : Summable (fun d : ℕ => r ^ (j + d) * lemmaVInverseDepthMax Q a (j + d)) := by
    -- Keep the descendant depth symbolic: unfolding the concrete four-level
    -- cell family here needlessly enumerates all 9^4 cubes during elaboration.
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (summable_nat_add_iff j).2 hsQ
  have hseries : Summable (fun d : ℕ => r ^ d * lemmaVInverseDepthMax Q a (j + d)) := by
    have hmul := htail.mul_left (r⁻¹ ^ j)
    have hcancel : r⁻¹ ^ j * r ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    have heq : (fun d : ℕ => r ^ d * lemmaVInverseDepthMax Q a (j + d)) =
        fun d => r⁻¹ ^ j * (r ^ (j + d) * lemmaVInverseDepthMax Q a (j + d)) := by
      funext d
      rw [pow_add]
      calc
        r ^ d * lemmaVInverseDepthMax Q a (j + d) =
            1 * (r ^ d * lemmaVInverseDepthMax Q a (j + d)) := by ring
        _ = (r⁻¹ ^ j * r ^ j) *
            (r ^ d * lemmaVInverseDepthMax Q a (j + d)) := by rw [hcancel]
        _ = r⁻¹ ^ j *
            (r ^ j * r ^ d * lemmaVInverseDepthMax Q a (j + d)) := by ring
    rw [heq]
    exact hmul
  have hsR : Summable (fun d : ℕ => r ^ d * lemmaVInverseDepthMax R a d) := by
    simpa only [r, q₀] using lemmaVInverseHistory_summable R hEllR hq₀
  have hsumle :
      (∑' d : ℕ, r ^ d * lemmaVInverseDepthMax R a d) ≤
        ∑' d : ℕ, r ^ d * lemmaVInverseDepthMax Q a (j + d) :=
    hsR.tsum_le_tsum (fun d => by
      exact mul_le_mul_of_nonneg_left
        (aoCir_inverseDepth_nested_bound Q R j d hR) (pow_nonneg hr.le d)) hseries
  have hhist : lemmaVInverseHistory R a q₀ =
      (1 - r) * ∑' d : ℕ, r ^ d * lemmaVInverseDepthMax R a d := by
    simp only [lemmaVInverseHistory, r]
  rw [hhist]
  have hαeq : r = aoCirInverseHistoryDiscount := by
    exact hα.trans rfl
  rw [hαeq] at hsumle
  rw [hαeq]
  have hcoef' : 0 ≤ 1 - aoCirInverseHistoryDiscount := by
    rw [← hαeq]
    exact hcoef
  exact mul_le_mul_of_nonneg_left hsumle hcoef'

/-- A finite descendant-layer maximum of complete histories is bounded by the
single geometric series of the combined descendant-depth maxima. The starting
depth remains symbolic so Lean does not enumerate a concrete cell family. -/
theorem pureFlux_source_tile_history_le_combined_depth_series
    (Q : TriadicCube 2) (j : ℕ) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    pureFluxSourceTileHistory Q j a ≤
      (1 - aoCirInverseHistoryDiscount) *
        ∑' d : ℕ, aoCirInverseHistoryDiscount ^ d *
          lemmaVInverseDepthMax Q a (j + d) := by
  classical
  unfold pureFluxSourceTileHistory
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j)
  intro R hR
  exact aoCir_tile_inverseHistory_le_parent_depth_series Q R a j hEll hR

end
end ASDExplicitGamma.AllOrder
