module

public import ASDExplicitGamma.Main.PanelComparison
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
public import Mathlib.Tactic.FieldSimp

/-! The deterministic one-panel comparison. The statement is that of
`main_panel_endpoint_bound_of_recurrence_fields`, over the `PanelEndpoints`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike

/-- One actual affine-comparison panel is bounded by the outward recurrence
map certified in `mainReturn_certificate`. -/
theorem main_panel_endpoint_bound
    {f : ℝ → ℝ} {a b : ℝ} (e : PanelEndpoints)
    (hab : a ≤ b) (hlen : b - a = (1 / 8 : ℝ))
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hderiv : ∀ᵐ t, t ∈ Icc a b →
      deriv f t ≤ (e.aUpper : ℝ) / (Spike.gridScale : ℝ) -
        (e.ellLower : ℝ) / (Spike.gridScale : ℝ) * f t)
    (hfnn : ∀ t ∈ Icc a b, 0 ≤ f t)
    (hfields : panelRecurrenceFields e) :
    f b ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) * f a +
      (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := by
  rcases hfields with ⟨hellPos, _hell, ha, hdecLo, hdecHi, hoff⟩
  have hG : 0 < (Spike.gridScale : ℝ) := by
    norm_num [Spike.gridScale]
  have hellG : 0 < (e.ellLower : ℝ) / (Spike.gridScale : ℝ) :=
    div_pos hellPos hG
  have hcomparison := panel_comparison hab hf hellG hderiv
  let decay : ℝ := Real.exp (-((e.ellLower : ℝ) /
    (8 * (Spike.gridScale : ℝ))))
  have hExpEq : Real.exp (-((e.ellLower : ℝ)) /
      (8 * (Spike.gridScale : ℝ))) = decay := by
    unfold decay
    congr 1
    rw [neg_div]
  have hdecayArg : -((e.ellLower : ℝ) / (8 * (Spike.gridScale : ℝ))) =
      -((e.ellLower : ℝ) / (Spike.gridScale : ℝ)) * (b - a) := by
    rw [hlen]
    ring
  have hdecayPanel : Real.exp
      (-((e.ellLower : ℝ) / (Spike.gridScale : ℝ)) * (b - a)) = decay := by
    unfold decay
    rw [← hdecayArg]
  have hdecLo' : (e.rhoLower : ℝ) / (Spike.gridScale : ℝ) ≤ decay := by
    rw [← hExpEq]
    exact hdecLo
  have hdecHi' : decay ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) := by
    rw [← hExpEq]
    exact hdecHi
  have hfa : 0 ≤ f a := hfnn a ⟨le_rfl, hab⟩
  have hremain : 1 - decay ≤
      ((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) /
        (Spike.gridScale : ℝ) := by
    have hGsub : 1 - (e.rhoLower : ℝ) / (Spike.gridScale : ℝ) =
        ((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) /
          (Spike.gridScale : ℝ) := by
      field_simp [hG.ne']
    rw [← hGsub]
    linarith [hdecLo']
  have hforcing :
      ((e.aUpper : ℝ) / (Spike.gridScale : ℝ)) * (1 - decay) /
          ((e.ellLower : ℝ) / (Spike.gridScale : ℝ)) ≤
        (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hremain ha
    have hgoal : ((e.aUpper : ℝ) *
        (((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) /
          (Spike.gridScale : ℝ))) /
          (e.ellLower : ℝ) ≤ (e.offsetUpper : ℝ) /
          (Spike.gridScale : ℝ) := by
      apply (div_le_iff₀ hellPos).2
      calc
        (e.aUpper : ℝ) *
            (((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) /
              (Spike.gridScale : ℝ)) ≤
          ((e.offsetUpper : ℝ) * (e.ellLower : ℝ)) /
            (Spike.gridScale : ℝ) := by
              have hleft : (e.aUpper : ℝ) *
                  (((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) /
                    (Spike.gridScale : ℝ)) =
                  ((e.aUpper : ℝ) *
                    ((Spike.gridScale : ℝ) - (e.rhoLower : ℝ))) /
                    (Spike.gridScale : ℝ) := by
                field_simp [hG.ne']
              rw [hleft]
              rw [div_le_div_iff_of_pos_right hG]
              exact hoff
        _ = ((e.offsetUpper : ℝ) /
              (Spike.gridScale : ℝ)) * (e.ellLower : ℝ) := by
              field_simp [hG.ne']
    calc
      _ = ((e.aUpper : ℝ) * (1 - decay)) / (e.ellLower : ℝ) := by
        field_simp [hG.ne', hellPos.ne']
      _ ≤ ((e.aUpper : ℝ) *
          (((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) /
            (Spike.gridScale : ℝ))) /
          (e.ellLower : ℝ) := by
        rw [div_le_div_iff_of_pos_right hellPos]
        exact hscaled
      _ ≤ (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := hgoal
  have hmap : panelMap
      ((e.aUpper : ℝ) / (Spike.gridScale : ℝ))
      ((e.ellLower : ℝ) / (Spike.gridScale : ℝ))
      (b - a) (f a) ≤
        (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) * f a +
          (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := by
    unfold panelMap
    rw [hdecayPanel]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hdecHi' hfa) hforcing
  exact hcomparison.trans hmap


end ASDExplicitGamma.Main

end
