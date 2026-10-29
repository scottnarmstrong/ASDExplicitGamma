module

public import ASDExplicitGamma.Scalar.UpperCellEnergyHistoryEnvelope

/-! Eliminate the auxiliary depth without dividing by a possibly zero load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

/-- A nonnegative prefactor is retained through the complete depth selection,
including its zero case. -/
theorem upper_cell_scaled_history_envelope {E C x q : ℝ}
    (hC : 0≤C) (hx : 0≤x) (hq : 1<q) (hq2 : q≤2)
    (hdepth : ∀ j : ℕ, x/q^j ≤ 2/5 →
      E ≤ C*(Real.sqrt (q^j)*(1+(5/4:ℝ)*(x/q^j)))) : E ≤ C*(1+3*x) := by
  by_cases hz : C=0
  · have hj : ∃ j : ℕ, x/q^j ≤ 2/5 := by
      by_cases hs : x≤2/5
      · exact ⟨0,by simpa using hs⟩
      · obtain ⟨j,hj,_⟩ := upper_cell_history_depth_choice (lt_of_not_ge hs) hq hq2
        exact ⟨j,hj⟩
    obtain ⟨j,hj⟩ := hj
    simpa only [hz,zero_mul] using hdepth j hj
  have hp : 0<C := lt_of_le_of_ne hC (Ne.symm hz)
  have he : E/C ≤ 1+3*x := upper_cell_history_linear_envelope hx hq hq2 (by
    intro j hj
    exact (div_le_iff₀ hp).2 (by simpa only [mul_comm] using hdepth j hj))
  exact (div_le_iff₀ hp).mp he |>.trans_eq (mul_comm _ _)

end ASDExplicitGamma.Scalar
