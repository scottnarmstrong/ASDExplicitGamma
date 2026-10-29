module

public import ASDExplicitGamma.Native.HeatMomentRoundedWeights

/-! Literal moment budget used inside one certified heat pass. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
open scoped BigOperators
noncomputable section

/-- The complete producer moment numerator, before taking its twentieth root. -/
def heatPassMomentBudget (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base y : ℚ) : ℚ :=
  let forcing := (List.range 20).map fun j => nativeHeatForcingAt old frames fixed y (j+1)
  nativeUp (base+((List.range 20).map fun j => coef.getD (j+1) 0*forcing.getD j 0/(20-j:ℕ)).sum)

theorem heat_pass_eq_min_root (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base y : ℚ) :
    nativeHeatPass old frames coef fixed base y =
      min y (nativeRootUp (heatPassMomentBudget old frames coef fixed base y) 20) := rfl

/-- List-dot-product identity used to connect the exact producer base to the
finite source moment sum, with no unstated list padding convention. -/
theorem heat_list_dot_eq_sum (a b : List ℚ) (hlen : a.length = b.length) :
    (List.zipWith (·*·) a b).sum = ∑ j ∈ Finset.range a.length,a.getD j 0*b.getD j 0 := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [List.length_cons]
      rw [Finset.sum_range_succ']
      simpa [List.zipWith,add_comm] using congrArg (fun q : ℚ => x*y+q) (ih ys hlen')

/-- The rounded base bounds the entire initial moment contribution. -/
theorem heat_initial_sum_le_rounded_base (coef init : List ℚ)
    (hc : coef.length = 21) (hi : init.length = 21) :
    (∑ j ∈ Finset.range 21,(coef.getD j 0:ℝ)*(init.getD j 0:ℝ)) ≤ (nativeHeatBase coef init:ℝ) := by
  have he := heat_list_dot_eq_sum coef init (hc.trans hi.symm)
  rw [hc] at he
  have hh := nativeUp_ge (List.zipWith (·*·) coef init).sum
  rw [he] at hh
  unfold nativeHeatBase
  rw [he]
  exact_mod_cast hh

/-- Literal list range sums agree with the finite analytical index set. -/
theorem heat_list_range_sum (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n,f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]

/-- Explicit source forcing sum inside the literal producer budget. -/
theorem heat_pass_budget_formula (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base y : ℚ) :
    heatPassMomentBudget old frames coef fixed base y =
      nativeUp (base+∑ j ∈ Finset.range 20,coef.getD (j+1) 0*
        nativeHeatForcingAt old frames fixed y (j+1)/(20-j:ℕ)) := by
  unfold heatPassMomentBudget
  dsimp only
  rw [heat_list_range_sum]
  congr 2

/-- The augmented forcing coordinate is zero; shifting its positive degrees
matches the producer's20-entry forcing list exactly. -/
theorem heat_forcing_sum_shift (coef : List ℚ) (E : ℕ → ℚ) :
    (∑ j ∈ Finset.range 21,coef.getD j 0*(if j=0 then 0 else E j)/(21-j:ℕ)) =
      ∑ j ∈ Finset.range 20,coef.getD (j+1) 0*E (j+1)/(20-j:ℕ) := by
  rw [show 21=20+1 from rfl,Finset.sum_range_succ']
  have he (j : ℕ) : 20+1-(j+1)=20-j := by omega
  simp [he]

/-- The whole initial-plus-forcing row lies below the outward pass numerator. -/
theorem heat_pass_budget_ge (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base y : ℚ) :
    base+(∑ j ∈ Finset.range 21,coef.getD j 0*
      (if j=0 then 0 else nativeHeatForcingAt old frames fixed y j)/(21-j:ℕ)) ≤
      heatPassMomentBudget old frames coef fixed base y := by
  rw [heat_forcing_sum_shift,heat_pass_budget_formula]
  exact nativeUp_ge _

end
end ASDExplicitGamma.Native
