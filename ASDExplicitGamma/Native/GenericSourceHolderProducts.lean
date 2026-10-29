module

public import ASDExplicitGamma.Native.GenericSourceHolderMinima

/-! The sharp L20 source products with one and two L128 inverse factors.
They consume the interpolated trace minima with ell=5/27 and 2ell=10/27. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The exact one-factor Holder order; the trace factor is not raised to 60. -/
theorem native_source_holder_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P F : Ω → ℝ)
    (hP : AEStronglyMeasurable P μ) (hF : AEStronglyMeasurable F μ)
    (b u : ℝ≥0∞) (hb : eLpNorm' P 128 μ ≤ b)
    (hu : eLpNorm' F (640/27) μ ≤ u) :
    eLpNorm' (fun ω => P ω*F ω) 20 μ ≤ b*u := by
  have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm' (p := 128) (q := 640/27) (r := 20)
    hP hF (fun x y : ℝ => x*y) 1
    (Filter.Eventually.of_forall fun _ => by simp only [nnnorm_mul,one_mul,le_refl])
    (by norm_num) (by norm_num) (by norm_num)
  have hh' : eLpNorm' (fun ω => P ω*F ω) 20 μ ≤ eLpNorm' P 128 μ*eLpNorm' F (640/27) μ := by
    simpa only [ENNReal.coe_one,one_mul] using hh
  exact hh'.trans (mul_le_mul' hb hu)

/-- Squaring the L128 inverse factor gives precisely its L64 square cap. -/
theorem native_source_holder_inverse_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P : Ω → ℝ) (hP : AEStronglyMeasurable P μ)
    (b : ℝ≥0∞) (hb : eLpNorm' P 128 μ ≤ b) :
    eLpNorm' (fun ω => (P ω)^2) 64 μ ≤ b^2 := by
  have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm' (p := 128) (q := 128) (r := 64)
    hP hP (fun x y : ℝ => x*y) 1
    (Filter.Eventually.of_forall fun _ => by simp only [nnnorm_mul,one_mul,le_refl])
    (by norm_num) (by norm_num) (by norm_num)
  have hh' : eLpNorm' (fun ω => (P ω)^2) 64 μ ≤ eLpNorm' P 128 μ*eLpNorm' P 128 μ := by
    simpa only [pow_two,ENNReal.coe_one,one_mul] using hh
  exact hh'.trans (by simpa only [pow_two] using mul_le_mul' hb hb)

/-- The exact two-factor Holder order, with the square of the inverse cap. -/
theorem native_source_holder_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (P F : Ω → ℝ)
    (hP : AEStronglyMeasurable P μ) (hF : AEStronglyMeasurable F μ)
    (b u : ℝ≥0∞) (hb : eLpNorm' P 128 μ ≤ b)
    (hu : eLpNorm' F (320/11) μ ≤ u) :
    eLpNorm' (fun ω => (P ω)^2*F ω) 20 μ ≤ b^2*u := by
  have hp2 : AEStronglyMeasurable (fun ω => (P ω)^2) μ := hP.pow 2
  have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm' (p := 64) (q := 320/11) (r := 20)
    hp2 hF (fun x y : ℝ => x*y) 1
    (Filter.Eventually.of_forall fun _ => by simp only [nnnorm_mul,one_mul,le_refl])
    (by norm_num) (by norm_num) (by norm_num)
  have hh' : eLpNorm' (fun ω => (P ω)^2*F ω) 20 μ ≤
      eLpNorm' (fun ω => (P ω)^2) 64 μ*eLpNorm' F (320/11) μ := by
    simpa only [ENNReal.coe_one,one_mul] using hh
  exact hh'.trans
    (mul_le_mul' (native_source_holder_inverse_square μ P hP b hb) hu)

end
end ASDExplicitGamma.Native
