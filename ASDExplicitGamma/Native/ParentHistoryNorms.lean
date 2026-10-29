module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Exact square-root norm identities for the discounted physical history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Square-rooting a nonnegative energy halves its moment order exactly. -/
theorem parent_history_sqrt_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω,0 ≤ f ω) (p : ℝ≥0∞) :
    eLpNorm (fun ω => Real.sqrt (f ω)) p μ=
      eLpNorm f (p*ENNReal.ofReal (1/2:ℝ)) μ ^ (1/2:ℝ) := by
  have he : (fun ω => Real.sqrt (f ω))=(fun ω => ‖f ω‖^(1/2:ℝ)) := by
    funext ω
    rw [Real.norm_of_nonneg (hf0 ω),Real.sqrt_eq_rpow]
  rw [he,eLpNorm_norm_rpow f hf (by norm_num : (0:ℝ)<1/2)]

/-- Conversion from an extended history to real values preserves the norm
only after almost-everywhere finiteness has been proved. -/
theorem parent_history_toReal_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Ω → ℝ≥0∞)
    (hF : ∀ᵐ ω ∂μ,F ω ≠ ⊤) (p : ℝ≥0∞) :
    eLpNorm (fun ω => (F ω).toReal) p μ=eLpNorm F p μ := by
  calc
    _ = eLpNorm (ENNReal.ofReal ∘ (fun ω => (F ω).toReal)) p μ :=
      (eLpNorm_ofReal _ (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))).symm
    _ = _ := eLpNorm_congr_ae (ofReal_toReal_ae_eq (hF.mono (fun _ h => lt_top_iff_ne_top.mpr h)))

/-- A fourth-moment bound on the square-root history gives exactly the
second-moment square bound on the history. -/
theorem parent_history_square_of_sqrt_L4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hf0 : ∀ ω,0 ≤ f ω)
    (A : ℝ) (hA : 0 ≤ A)
    (hroot : eLpNorm (fun ω => Real.sqrt (f ω)) 4 μ ≤ ENNReal.ofReal A) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (A^2) := by
  have he := parent_history_sqrt_norm μ f hf hf0 4
  have hp : (4:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ)=2 := by
    calc
      _ = ENNReal.ofReal (4:ℝ)*ENNReal.ofReal (1/2:ℝ) := by norm_num
      _ = ENNReal.ofReal ((4:ℝ)*(1/2)) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ = _ := by norm_num
  rw [hp] at he
  rw [he] at hroot
  have hh := ENNReal.rpow_le_rpow hroot (by norm_num : (0:ℝ)≤2)
  rw [←ENNReal.rpow_mul] at hh
  norm_num only [show (1/2:ℝ)*2=1 by norm_num,ENNReal.rpow_one,ENNReal.rpow_two] at hh
  exact hh.trans_eq (ENNReal.ofReal_pow hA 2).symm

/-- The centered L20 history pays the exact L4 norm of its square root. -/
theorem parent_history_sqrt_L4_le_L20
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Ω → ℝ) (hC : MemLp C 20 μ) (hC0 : ∀ ω,0 ≤ C ω) :
    eLpNorm (fun ω => Real.sqrt (C ω)) 4 μ ≤
      ENNReal.ofReal (Real.sqrt (eLpNorm C 20 μ).toReal) := by
  have he := parent_history_sqrt_norm μ C hC.aestronglyMeasurable hC0 4
  have hp : (4:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ)=2 := by
    calc
      _ = ENNReal.ofReal (4:ℝ)*ENNReal.ofReal (1/2:ℝ) := by norm_num
      _ = ENNReal.ofReal ((4:ℝ)*(1/2)) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ = _ := by norm_num
  rw [hp] at he
  rw [he,Real.sqrt_eq_rpow,←ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal hC.eLpNorm_ne_top]
  exact ENNReal.rpow_le_rpow (eLpNorm_le_eLpNorm_of_exponent_le
    (f := C) (μ := μ) (by norm_num : (2:ℝ≥0∞)≤20)) (by norm_num)

end
end ASDExplicitGamma.Native
