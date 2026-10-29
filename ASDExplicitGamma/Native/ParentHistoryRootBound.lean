module

public import ASDExplicitGamma.Native.ParentHistoryRareNorms

/-! Correlated L4 square-root payment for the complete physical history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A nonnegative scalar factor preserves the literal probability norm. -/
theorem parent_history_nonneg_const_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (p : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) :
    eLpNorm (fun ω => c*f ω) p μ=ENNReal.ofReal c*eLpNorm f p μ := by
  change eLpNorm (c • f) p μ=_
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hc]

/-- A pathwise complete-history restoration is paid by the ACTUAL
correlated center and rare bank. All norm assumptions here are analytic
data; the source export discharges them from the proved model laws. -/
theorem parent_history_root_payment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X C G B R : Ω → ℝ) (hX : AEStronglyMeasurable X μ)
    (hX0 : ∀ ω,0 ≤ X ω) (hC : MemLp C 20 μ) (hC0 : ∀ ω,0 ≤ C ω)
    (hG8 : MemLp G 8 μ) (hR128 : MemLp R 128 μ) (hR0 : ∀ ω,0 ≤ R ω)
    (b eps g4 g8 : ℝ) (hb : 0 ≤ b) (heps : 0 ≤ eps) (hg4 : 0 ≤ g4) (hg8 : 0 ≤ g8)
    (hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal eps)
    (hG4cap : eLpNorm G 4 μ ≤ ENNReal.ofReal g4)
    (hG8cap : eLpNorm G 8 μ ≤ ENNReal.ofReal g8)
    (hB : ∀ᵐ ω ∂μ,B ω ≤ b+R ω)
    (hrestore : ∀ᵐ ω ∂μ,Real.sqrt (X ω) ≤ Real.sqrt (C ω)+|G ω| *Real.sqrt (2*B ω)) :
    eLpNorm X 2 μ ≤ ENNReal.ofReal
      ((Real.sqrt (eLpNorm C 20 μ).toReal+Real.sqrt (2*b)*g4+
        Real.sqrt 2*(g8*Real.sqrt eps))^2) := by
  let A := fun ω => Real.sqrt (C ω)
  let D := fun ω => Real.sqrt (2*b)* |G ω|
  let E := fun ω => Real.sqrt 2*(|G ω| *Real.sqrt (R ω))
  have hxroot : AEStronglyMeasurable (fun ω => Real.sqrt (X ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hX
  have hpoint : ∀ᵐ ω ∂μ,Real.sqrt (X ω) ≤ (A ω+D ω)+E ω := by
    filter_upwards [hB,hrestore] with ω hsplit hx
    have hroot : Real.sqrt (2*B ω) ≤ Real.sqrt (2*b)+Real.sqrt 2*Real.sqrt (R ω) := by
      calc
        _ ≤ Real.sqrt (2*b+2*R ω) := Real.sqrt_le_sqrt
          ((mul_le_mul_of_nonneg_left hsplit (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
        _ ≤ Real.sqrt (2*b)+Real.sqrt (2*R ω) := by
          apply Real.sqrt_le_iff.mpr
          refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),?_⟩
          have hs1 := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hb)
          have hs2 := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) (hR0 ω))
          nlinarith only [hs1,hs2,mul_nonneg (Real.sqrt_nonneg (2*b)) (Real.sqrt_nonneg (2*R ω))]
        _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2) (R ω)]
    exact hx.trans ((add_le_add_right (mul_le_mul_of_nonneg_left hroot (abs_nonneg _)) _).trans_eq
      (by dsimp only [A,D,E]; ring))
  have hA := parent_history_sqrt_L4_le_L20 μ C hC hC0
  have hgabs : eLpNorm (fun ω => |G ω|) 4 μ=eLpNorm G 4 μ := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm G hG8.aestronglyMeasurable
  have hD : eLpNorm D 4 μ ≤ ENNReal.ofReal (Real.sqrt (2*b)*g4) := by
    rw [show D=(fun ω => Real.sqrt (2*b)* |G ω|) from rfl,
      parent_history_nonneg_const_norm μ _ 4 _ (Real.sqrt_nonneg _),hgabs]
    exact (mul_le_mul_of_nonneg_left hG4cap (show (0:ℝ≥0∞)≤ENNReal.ofReal (Real.sqrt (2*b)) from bot_le)).trans_eq (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  have hE : eLpNorm E 4 μ ≤ ENNReal.ofReal (Real.sqrt 2*(g8*Real.sqrt eps)) := by
    rw [show E=(fun ω => Real.sqrt 2*(|G ω| *Real.sqrt (R ω))) from rfl,
      parent_history_nonneg_const_norm μ _ 4 _ (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (parent_history_rare_product_L4 μ G R hG8 hR128 hR0 eps g8 heps hg8 hRcap hG8cap) (show (0:ℝ≥0∞)≤ENNReal.ofReal (Real.sqrt 2) from bot_le)).trans_eq
      (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  have hmono : eLpNorm (fun ω => Real.sqrt (X ω)) 4 μ ≤ eLpNorm ((A+D)+E) 4 μ := by
    apply eLpNorm_mono_ae_real hxroot
    filter_upwards [hpoint] with ω hω
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact hω
  have htriangle : eLpNorm ((A+D)+E) 4 μ ≤ eLpNorm A 4 μ+eLpNorm D 4 μ+eLpNorm E 4 μ :=
    (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞)≤4)).trans
      (add_le_add_left (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞)≤4)) _)
  have htotal := hmono.trans (htriangle.trans (add_le_add (add_le_add hA hD) hE))
  have hcoef0 : 0 ≤ Real.sqrt (eLpNorm C 20 μ).toReal+Real.sqrt (2*b)*g4+
      Real.sqrt 2*(g8*Real.sqrt eps) := by positivity
  have hrootcap : eLpNorm (fun ω => Real.sqrt (X ω)) 4 μ ≤ ENNReal.ofReal
      (Real.sqrt (eLpNorm C 20 μ).toReal+Real.sqrt (2*b)*g4+Real.sqrt 2*(g8*Real.sqrt eps)) := by
    rw [ENNReal.ofReal_add (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hg4))
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hg8 (Real.sqrt_nonneg _))),
      ENNReal.ofReal_add (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hg4)]
    exact htotal
  exact parent_history_square_of_sqrt_L4 μ X hX hX0 _ hcoef0 hrootcap

end
end ASDExplicitGamma.Native
