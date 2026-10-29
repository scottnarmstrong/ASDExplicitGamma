module

public import ASDExplicitGamma.Inverse.PhysicalGaussianMissingWave
public import ASDExplicitGamma.Inverse.WeightedLocalizationResetSeries

/-! Actual protected reset waves with their source physical clock factored exactly. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The actual old cutoff label at reset depth x+1. -/
def physicalResetOldLabel (Q : TriadicCube 2) (H0 : ℕ) (hk : ℕ × ℕ) : ℤ :=
  Q.scale-(localizationResetAbscissa (H0-38) hk.1 hk.2+1:ℕ)

/-- The complete wave after extracting gamma*(D+x)*3^(2*gamma*D), with the
old-frame factor 3^(2*gamma*x) retained. Its clock is exactly 3^(4*gamma*x). -/
def physicalResetWave (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let j := physicalResetOldLabel Q H0 hk
  let x : ℝ := localizationResetAbscissa (H0-38) hk.1 hk.2
  let D : ℝ := (N:ℝ)-(Q.scale:ℝ)+1
  ((3:ℝ)^(2*A.gamma*(x-D))/(A.gamma*((N:ℝ)-(j:ℝ))))*
    physicalMissingWave A j Q.scale N a c (weights hk) ω

theorem physical_reset_old_label_lt (Q : TriadicCube 2) (H0 : ℕ) (hk : ℕ × ℕ) :
    physicalResetOldLabel Q H0 hk < Q.scale := by unfold physicalResetOldLabel; omega

/-- Exact source gap: N-j_old=D+x, without absorbing gamma in another clock. -/
theorem physical_reset_gap_eq (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ) (hk : ℕ × ℕ) :
    (N:ℝ)-(physicalResetOldLabel Q H0 hk:ℝ) =
      ((N:ℝ)-(Q.scale:ℝ)+1)+(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ) := by
  unfold physicalResetOldLabel
  push_cast
  ring

/-- Every actual old frame is in the protected native past. -/
theorem physical_reset_old_label_protected (Q : TriadicCube 2) (H0 : ℕ) (hH : 333 ≤ H0) (hk : ℕ × ℕ) :
    physicalResetOldLabel Q H0 hk ≤ Q.scale-(H0:ℤ)+40 := by
  unfold physicalResetOldLabel localizationResetAbscissa localizationProfileDepth
  omega

/-- Ordinary sample measurability survives the deterministic physical normalization. -/
theorem physical_reset_wave_measurable (A : ABKModel 2) (Q : TriadicCube 2) (N : ℤ) (H0 : ℕ)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ) (hk : ℕ × ℕ) :
    Measurable (physicalResetWave A Q N H0 a c weights hk) :=
  measurable_const.mul (physical_missing_wave_measurable A _ _ _ a c _)

end
end ASDExplicitGamma.Inverse
