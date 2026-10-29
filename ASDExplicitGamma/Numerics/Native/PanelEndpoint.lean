module
public import ASDExplicitGamma.Numerics.Native.PanelSum

/-! The earlier-label 3/50 start is kept separate from the completed source mean in the panel. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics

noncomputable def nativePanelEndpoint (fields : List ℝ) (frame b0 inverseCost : ℝ) : ℝ :=
  frame*((3/50 : ℝ)+b0+(∫ s in (0 : ℝ)..1, nativePanelValue fields s)+inverseCost)

theorem nativePanelEndpoint_bound (fields : List ℝ) (frame b0 inverseCost : ℝ)
    (frameI b0I inverseCostI : QInterval) (mean cap : ℚ)
    (hf : QInterval.Contains frameI frame) (hb : QInterval.Contains b0I b0)
    (hi : QInterval.Contains inverseCostI inverseCost)
    (hf0 : 0 ≤ frameI.lo)
    (hmean : (∫ s in (0 : ℝ)..1, nativePanelValue fields s) ≤ (mean : ℝ))
    (htop : 0 ≤ (3/50 : ℚ)+b0I.hi+mean+inverseCostI.hi)
    (hcap : frameI.hi*((3/50 : ℚ)+b0I.hi+mean+inverseCostI.hi) ≤ cap) :
    nativePanelEndpoint fields frame b0 inverseCost ≤ (cap : ℝ) := by
  have hlo := (Rat.cast_le (K := ℝ)).2 hf0
  simp only [Rat.cast_zero] at hlo
  have hframe : 0 ≤ frame := hlo.trans hf.1
  have htopR := (Rat.cast_le (K := ℝ)).2 htop
  simp only [Rat.cast_zero] at htopR
  have hinner : (3/50 : ℝ)+b0+(∫ s in (0 : ℝ)..1, nativePanelValue fields s)+inverseCost ≤
      (((3/50 : ℚ)+b0I.hi+mean+inverseCostI.hi : ℚ) : ℝ) := by
    have h := add_le_add (add_le_add (add_le_add (le_refl (3/50 : ℝ)) hb.2) hmean) hi.2
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using h
  have hprod := (mul_le_mul_of_nonneg_left hinner hframe).trans
    (mul_le_mul_of_nonneg_right hf.2 htopR)
  have hc := (Rat.cast_le (K := ℝ)).2 hcap
  exact hprod.trans (by simpa only [Rat.cast_mul] using hc)

end ASDExplicitGamma.Numerics.Native
