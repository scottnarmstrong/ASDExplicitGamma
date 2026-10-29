module

public import ASDExplicitGamma.Scalar.LawShiftMeasure
public import Algsuperdiff.Section3.Cutoff.Law

/-! Exact scale shifts on the convergent cutoff carrier and its canonical probability law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

/-- The scale shift on every genuine convergent-tail realization. -/
noncomputable def cutoffScaleShift {d : ℕ} (γ : ℝ) (m : ℤ) (ω : Cutoff.CutoffSample d) :
    Cutoff.CutoffSample d := ⟨shellScaleShift γ m ω.1,shell_scale_shift_lower_tail_good γ m ω⟩

/-- The honest carrier action is measurable. -/
theorem measurable_cutoff_scale_shift {d : ℕ} (γ : ℝ) (m : ℤ) :
    Measurable (cutoffScaleShift (d:=d) γ m) :=
  ((measurable_shell_scale_shift γ m).comp measurable_subtype_coe).subtype_mk

/-- The canonical induced cutoff-sample law is exactly invariant. -/
theorem cutoff_scale_shift_preserves_law {d : ℕ} (M : ABKModel d) (m : ℤ) :
    Measure.map (cutoffScaleShift M.gamma m) (Cutoff.cutoffSampleLaw M).toMeasure=
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hemb : MeasurableEmbedding (Subtype.val : Cutoff.CutoffSample d → Cutoff.ShellSeq d) :=
    MeasurableEmbedding.subtype_coe (Cutoff.measurableSet_lowerTailGoodSet d)
  apply hemb.map_injective
  rw [Measure.map_map measurable_subtype_coe (measurable_cutoff_scale_shift M.gamma m),
    Cutoff.map_cutoffSampleLaw_val]
  change Measure.map (shellScaleShift M.gamma m ∘ Subtype.val) (Cutoff.cutoffSampleLaw M).toMeasure=M.P.toMeasure
  rw [← Measure.map_map (measurable_shell_scale_shift M.gamma m) measurable_subtype_coe,
    Cutoff.map_cutoffSampleLaw_val,shell_scale_shift_preserves_law]

/-- The lower-infinite cutoff transforms as the literal rescaled series, on every sample. -/
theorem cutoff_scale_shift_value {d : ℕ} (γ : ℝ) (m n : ℤ) (ω : Cutoff.CutoffSample d)
    (x : Vec d) :
    Cutoff.cutoff n (cutoffScaleShift γ m ω) x=
      Real.rpow 3 (γ*((-m:ℤ):ℝ)) • Cutoff.cutoff (n+m) ω ((3:ℝ)^m • x) := by
  ext i j
  simp only [Cutoff.cutoff_apply_entry,Matrix.smul_apply,smul_eq_mul]
  change (∑' r : ℕ,ShellField.triadicScale γ (-m) (ω.1 (n-(r:ℤ)+m)) x i j)=_
  simp only [ShellField.triadicScale_apply,Matrix.smul_apply,smul_eq_mul,zpow_neg,inv_inv]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro r
  rw [show n-(r:ℤ)+m=n+m-(r:ℤ) by omega]

end ASDExplicitGamma.Scalar
