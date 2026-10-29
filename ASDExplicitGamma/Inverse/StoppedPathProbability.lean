module

public import ASDExplicitGamma.Inverse.StoppedRouteEvents

/-! The finite actual-route union proves the planar occupied path probability bound. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped BigOperators

/-- Even the larger all-route count fits the source radius margin at every
integer length, including the short-path endpoint cases. -/
theorem all_route_probability_cost (R : ℕ) :
    ((8:ℝ)^R)*Real.exp (-(49/10:ℝ)*((R+1:ℕ):ℝ)) ≤ Real.exp (-(R:ℝ)/2) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 4
  have h8 : (8:ℝ) ≤ Real.exp 3 := by
    norm_num [Finset.sum_range_succ,Nat.factorial] at he
    linarith only [he]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8) h8 R
  calc
    _ ≤ (Real.exp 3)^R*Real.exp (-(49/10:ℝ)*((R+1:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (3*(R:ℝ)-(49/10:ℝ)*((R+1:ℕ):ℝ)) := by
      rw [← Real.exp_nat_mul,← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      push_cast
      have hR : (0:ℝ) ≤ R := Nat.cast_nonneg _
      linarith only [hR]

/-- The actual shortest occupied path event obeys a bound stronger than the
source 6*exp(-R/2), from named mark/independence inputs and no cluster premise. -/
theorem shortest_occupied_path_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (x : BlockSite) (R : ℕ) :
    μ.real (shortestOccupiedLengthEvent B x R) ≤ Real.exp (-(R:ℝ)/2) := by
  have hc := shortest_event_subset_candidates B x R
  calc
    _ ≤ μ.real (⋃ r : BlockRoutes x R, candidateRouteEvent B x R r) := measureReal_mono hc
    _ ≤ ∑ r : BlockRoutes x R, μ.real (candidateRouteEvent B x R r) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _r : BlockRoutes x R, Real.exp (-(49/10:ℝ)*((R+1:ℕ):ℝ)) :=
      Finset.sum_le_sum (fun r _ => candidate_route_probability μ B q hB hq0 hq x R r)
    _ = ((8:ℝ)^R)*Real.exp (-(49/10:ℝ)*((R+1:ℕ):ℝ)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,block_routes_card,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ _ := all_route_probability_cost R

end ASDExplicitGamma.Inverse
