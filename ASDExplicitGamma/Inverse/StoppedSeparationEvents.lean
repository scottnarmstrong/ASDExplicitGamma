module

public import ASDExplicitGamma.Inverse.StoppedHeightPayments
public import ASDExplicitGamma.Inverse.StoppedClusterReach
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The exact finite-root separation event and its source probability payment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- All fine starting indices in the root at deterministic depth h. -/
abbrev RootStartingIndex (h : ℕ) := Fin 2 → Fin (3^h)

theorem root_starting_card (h : ℕ) : Fintype.card (RootStartingIndex h) = 3^(2*h) := by
  simp only [RootStartingIndex,Fintype.card_fun,Fintype.card_fin]
  rw [← pow_mul,Nat.mul_comm h 2]

/-- The conservative source block radius after converting the fine radius and
retaining the endpoint enlargement. -/
def separationRadius (h : ℕ) : ℕ := ⌊heightExponent h/3-1⌋₊

/-- The actual separation-failure event is a union of occupied-component
radius events over the full root-relative deterministic population. -/
def separationFailure {Ω : Type*} (B : PlanarMarks Ω) (h : ℕ)
    (x : RootStartingIndex h → BlockSite) : Set Ω :=
  ⋃ i : RootStartingIndex h, clusterReaches B (x i) (separationRadius h)

/-- Integer rounding costs less than the source prefactor ten. -/
theorem separation_radius_payment (h : ℕ) :
    Real.exp (-(separationRadius h:ℝ)/2) ≤ 10*Real.exp (-heightExponent h/6) := by
  have hf := Nat.lt_floor_add_one (a := heightExponent h/3-1)
  have hexp : Real.exp (-(separationRadius h:ℝ)/2) ≤ Real.exp (1-heightExponent h/6) := by
    apply Real.exp_le_exp.mpr
    change -(⌊heightExponent h/3-1⌋₊:ℝ)/2 ≤ 1-heightExponent h/6
    linarith only [hf]
  apply hexp.trans
  rw [sub_eq_add_neg,Real.exp_add]
  simpa only [neg_div] using! mul_le_mul_of_nonneg_right
    (Real.exp_one_lt_three.le.trans (by norm_num : (3:ℝ) ≤ 10)) (Real.exp_pos (-(heightExponent h/6))).le

/-- The complete root count yields the source (4.1) separation bound, then
its uniform exp(-Y_h/12) payment, without independence across starting sites. -/
theorem separation_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (h : ℕ) (hh : 333 ≤ h) (x : RootStartingIndex h → BlockSite) :
    μ.real (separationFailure B h x) ≤ Real.exp (-heightExponent h/12) := by
  calc
    _ ≤ ∑ i : RootStartingIndex h, μ.real (clusterReaches B (x i) (separationRadius h)) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : RootStartingIndex h, Real.exp (-(separationRadius h:ℝ)/2) :=
      Finset.sum_le_sum (fun i _ => cluster_radius_probability μ B q hB hq0 hq (x i) _)
    _ = (3:ℝ)^(2*h)*Real.exp (-(separationRadius h:ℝ)/2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,root_starting_card,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ 10*(3:ℝ)^(2*h)*Real.exp (-heightExponent h/6) := by
      have he := mul_le_mul_of_nonneg_left (separation_radius_payment h) (by positivity : (0:ℝ) ≤ 3^(2*h))
      nlinarith only [he]
    _ ≤ _ := separation_probability_payment h hh

end
end ASDExplicitGamma.Inverse
