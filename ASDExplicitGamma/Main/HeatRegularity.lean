module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.MeanValue

/-! Absolute continuity supplied by the actual half-line C1 heat theorem. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory

/-- The heat theorem's continuous derivative and right endpoint derivative
imply absolute continuity on the full insertion panel, including time zero. -/
theorem main_heat_absolutelyContinuous {f d : ℝ → ℝ}
    (hd : ContinuousOn d (Ici 0))
    (hpos : ∀ t ∈ Ioi 0, HasDerivAt f (d t) t)
    (hzero : HasDerivWithinAt f (d 0) (Ici 0) 0) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  have hdc : ContinuousOn d (Icc 0 1) := hd.mono Icc_subset_Ici_self
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  let K : NNReal := ⟨max C 0, le_max_right _ _⟩
  have hder (t : ℝ) (ht : t ∈ Icc 0 1) : HasDerivWithinAt f (d t) (Icc 0 1) t := by
    rcases ht.1.eq_or_lt with h | h
    · subst t
      exact hzero.mono Icc_subset_Ici_self
    · exact (hpos t h).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc 0 1) : ‖d t‖₊ ≤ K := by
    apply NNReal.coe_le_coe.mp
    exact (hC t ht).trans (le_max_left _ _)
  have hLip := (convex_Icc (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hder hbound
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hLip

end ASDExplicitGamma.Main
