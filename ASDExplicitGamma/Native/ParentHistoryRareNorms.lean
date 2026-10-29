module

public import ASDExplicitGamma.Native.ParentHistoryNorms
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Correlated rare-bank payment at the exact Gaussian fourth/eighth orders. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The square root of a nonnegative L128 reserve has its sharp L8 cap. -/
theorem parent_history_rare_sqrt_L8
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : MemLp R 128 μ) (hR0 : ∀ ω,0 ≤ R ω)
    (eps : ℝ) (heps : 0 ≤ eps) (hcap : eLpNorm R 128 μ ≤ ENNReal.ofReal eps) :
    eLpNorm (fun ω => Real.sqrt (R ω)) 8 μ ≤ ENNReal.ofReal (Real.sqrt eps) := by
  have he := parent_history_sqrt_norm μ R hR.aestronglyMeasurable hR0 8
  have hp : (8:ℝ≥0∞)*ENNReal.ofReal (1/2:ℝ)=4 := by
    calc
      _ = ENNReal.ofReal (8:ℝ)*ENNReal.ofReal (1/2:ℝ) := by norm_num
      _ = ENNReal.ofReal ((8:ℝ)*(1/2)) := (ENNReal.ofReal_mul (by norm_num)).symm
      _ = _ := by norm_num
  rw [hp] at he
  rw [he,Real.sqrt_eq_rpow,←ENNReal.ofReal_rpow_of_nonneg heps (by norm_num)]
  exact ENNReal.rpow_le_rpow ((eLpNorm_le_eLpNorm_of_exponent_le
    (f := R) (μ := μ) (by norm_num : (4:ℝ≥0∞)≤128)).trans hcap) (by norm_num)

/-- The shared center and rare inverse bank are paid by correlated Holder;
no independence is asserted or required. -/
theorem parent_history_rare_product_L4
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G R : Ω → ℝ) (hG : MemLp G 8 μ) (hR : MemLp R 128 μ)
    (hR0 : ∀ ω,0 ≤ R ω) (eps C : ℝ) (heps : 0 ≤ eps) (hC : 0 ≤ C)
    (hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal eps)
    (hGcap : eLpNorm G 8 μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => |G ω| *Real.sqrt (R ω)) 4 μ ≤ ENNReal.ofReal (C*Real.sqrt eps) := by
  have htriple : Real.HolderTriple 8 8 4 := by constructor <;> norm_num
  let parentHistoryRareHolder884 : ENNReal.HolderTriple 8 8 4 := by
    simpa only [ENNReal.ofReal_ofNat] using htriple.ennrealOfReal
  have hroot := parent_history_rare_sqrt_L8 μ R hR hR0 eps heps hRcap
  have hrootsm : AEStronglyMeasurable (fun ω => Real.sqrt (R ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hR.aestronglyMeasurable
  have hgsm : AEStronglyMeasurable (fun ω => |G ω|) μ := by
    simpa only [Real.norm_eq_abs] using hG.aestronglyMeasurable.norm
  have hgcap : eLpNorm (fun ω => |G ω|) 8 μ ≤ ENNReal.ofReal C := by
    simpa only [←Real.norm_eq_abs,eLpNorm_norm G hG.aestronglyMeasurable] using hGcap
  have hh := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 8) (q := 8) (r := 4)
    (fun x y : ℝ => x*y) 1 continuous_mul hgsm hrootsm
    (ae_of_all _ (fun ω => by simp [norm_mul]))
  calc
    _ ≤ eLpNorm (fun ω => |G ω|) 8 μ*eLpNorm (fun ω => Real.sqrt (R ω)) 8 μ := by
      simpa only [ENNReal.coe_one,one_mul] using hh
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (Real.sqrt eps) := mul_le_mul' hgcap hroot
    _ = _ := (ENNReal.ofReal_mul hC).symm

end
end ASDExplicitGamma.Native
