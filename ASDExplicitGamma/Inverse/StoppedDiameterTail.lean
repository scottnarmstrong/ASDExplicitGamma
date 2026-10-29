module

public import ASDExplicitGamma.Inverse.StoppedDiameterRadius
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The actual planar diameter field obeys the source exponential tail. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The source tail constant 200 applies to the exact radius-two field Z,
without any independence among its neighboring components. -/
theorem diameter_field_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (x : BlockSite) (t : ℝ) :
    μ.real {ω | ENNReal.ofReal t < diameterField B ω x} ≤ 200*Real.exp (-t/4) := by
  by_cases ht : 2 ≤ t
  · let R : ℕ := ⌊t/2-1⌋₊
    have hRle : (R:ℝ) ≤ t/2-1 := Nat.floor_le (by linarith only [ht])
    have hRlt : t/2-1 < (R:ℝ)+1 := Nat.lt_floor_add_one _
    have hcost : (((2*R+1:ℕ):ℝ≥0∞)) ≤ ENNReal.ofReal t := by
      have hh : ((2*R+1:ℕ):ℝ) ≤ t := by push_cast; linarith only [hRle]
      simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hh
    have hsub : {ω | ENNReal.ofReal t < diameterField B ω x} ⊆
        ⋃ y ∈ diameterRoots x, clusterReaches B y R := by
      intro ω hω
      apply diameter_exceed_subset_radius B x R
      exact lt_of_le_of_lt hcost hω
    calc
      _ ≤ μ.real (⋃ y ∈ diameterRoots x, clusterReaches B y R) := measureReal_mono hsub (measure_ne_top μ _)
      _ ≤ ∑ y ∈ diameterRoots x, μ.real (clusterReaches B y R) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _y ∈ diameterRoots x, Real.exp (-(R:ℝ)/2) :=
        Finset.sum_le_sum fun y _ => cluster_radius_probability μ B q hB hq0 hq y R
      _ = 25*Real.exp (-(R:ℝ)/2) := by
        rw [Finset.sum_const,nsmul_eq_mul,diameter_roots_card]
        norm_num only [Nat.cast_ofNat]
      _ ≤ 25*Real.exp (1-t/4) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith only [hRlt])) (by norm_num)
      _ ≤ 200*Real.exp (-t/4) := by
        rw [show 1-t/4 = 1+(-t/4) by ring,Real.exp_add]
        have he := Real.exp_one_lt_three.le
        have hp := Real.exp_pos (-t/4)
        nlinarith only [mul_le_mul_of_nonneg_right he hp.le,hp]

  · have hsmall : t < 2 := lt_of_not_ge ht
    have he := Real.add_one_le_exp (-t/4)
    have hb : (1:ℝ) ≤ 200*Real.exp (-t/4) := by linarith only [he,hsmall]
    exact (measureReal_le_one).trans hb

end
end ASDExplicitGamma.Inverse
