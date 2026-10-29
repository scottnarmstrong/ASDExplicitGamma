module

public import ASDExplicitGamma.Native.HeatStepAvg
public import ASDExplicitGamma.Native.HeatVHEATSourceNodeFinalGen

/-! The differential row of the pass lemmas for the `ns`-shell carrier: VHEAT at the configured
caps `X = frames.x`, `F = frames.raw`, `Y = y`, then the drift comparison with the configured
OLD coefficient and the comparison of the VHEAT error with the configured forcing at `y`; the
inequality is closed on `[0,1]` by continuity. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
open scoped ENNReal Topology

/-- A pointwise inequality of continuous functions on `(0,1)` extends to `[0,1]`. -/
theorem nativeHeatStep_le_on_Icc_of_Ioo {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (h : ∀ s ∈ Ioo (0 : ℝ) 1, f s ≤ g s) : ∀ s ∈ Icc (0 : ℝ) 1, f s ≤ g s := by
  have hu : ContinuousOn (fun s => g s - f s) (Icc (0 : ℝ) 1) := hg.sub hf
  have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ (fun s => g s - f s) ⁻¹' Ici 0) :=
    hu.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub : Ioo (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 ∩ (fun s => g s - f s) ⁻¹' Ici 0 := by
    intro s hs
    exact ⟨Ioo_subset_Icc_self hs, by simpa using sub_nonneg.mpr (h s hs)⟩
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at hcl
  intro s hs
  exact sub_nonneg.mp (by simpa using (hcl hs).2)

section Rows

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- The drift coefficient of the source row is below the configured OLD coefficient. -/
theorem nativeHeatStep_drift_le (hgen : NativeHeatGenNum ns) (hg : M.gamma ≤ gammaZero) :
    (0 ≤ (heatVHEATDriftEGen ns) M ∧
      (heatVHEATDriftEGen ns) M ≤ ((nativeHeatOldRowGen ns).e : ℝ)) ∧
    (heatVHEATDriftEGen ns) M * (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
        (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) ≤ (nativeHeatExpArgGen ns : ℝ) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have he0 : 0 ≤ (heatVHEATDriftEGen ns) M := by
    unfold heatVHEATDriftEGen
    positivity
  have heold : (heatVHEATDriftEGen ns) M ≤ ((nativeHeatOldRowGen ns).e : ℝ) := by
    unfold heatVHEATDriftEGen
    exact hgen.efactor M.gamma hg0 hg
  refine ⟨⟨he0, heold⟩, ?_⟩
  have hB : (3683 / 2500 : ℝ) ≤ (nativeHeatB : ℝ) := by
    have : (3683 / 2500 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    calc (3683 / 2500 : ℝ) = ((3683 / 2500 : ℚ) : ℝ) := by norm_num
      _ ≤ (nativeHeatB : ℝ) := Rat.cast_le.mpr this
  have hK : 0 ≤ (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  have hMm : 0 ≤ (nativeHeatM : ℝ) := by norm_num [nativeHeatM]
  have hpoly : 2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) + (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2 ≤
      2 * (nativeHeatK : ℝ) * (nativeHeatB : ℝ) + (nativeHeatM : ℝ) * (nativeHeatB : ℝ) ^ 2 := by
    have h1 : (3683 / 2500 : ℝ) ^ 2 ≤ (nativeHeatB : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hB 2
    nlinarith [mul_le_mul_of_nonneg_left hB hK, mul_le_mul_of_nonneg_left h1 hMm]
  have hpoly0 : 0 ≤ 2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
      (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2 := by positivity
  have hcast : (nativeHeatExpArgGen ns : ℝ) = ((nativeHeatOldRowGen ns).e : ℝ) *
      (2 * (nativeHeatK : ℝ) * (nativeHeatB : ℝ) + (nativeHeatM : ℝ) * (nativeHeatB : ℝ) ^ 2) := by
    unfold nativeHeatExpArgGen nativeHeatExpArg
    push_cast
    ring
  rw [hcast]
  exact mul_le_mul heold hpoly hpoly0 (he0.trans heold)

end Rows

end ASDExplicitGamma.Native

end
