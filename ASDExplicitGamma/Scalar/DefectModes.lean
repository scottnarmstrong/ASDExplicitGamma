module

public import ASDExplicitGamma.Scalar.DefectGSlotId
public import ASDExplicitGamma.Scalar.PhysicalResponse
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance

/-! Mode enumeration of the Gaussian shell series and the multiplier link `η_l = H_l / σ`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped InnerProductSpace

noncomputable section

/-- The white-basis mode in position `n` of the zero-padded enumeration, if any. -/
def eOpt (n : ℕ) : Option whiteBasisIndex := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  exact if h : ∃ l : whiteBasisIndex, Encodable.encode l = n then some h.choose else none

theorem eOpt_eq_some {n : ℕ} {l : whiteBasisIndex} :
    eOpt n = some l ↔ @Encodable.encode _ (Encodable.ofCountable whiteBasisIndex) l = n := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  unfold eOpt
  by_cases h : ∃ l' : whiteBasisIndex, Encodable.encode l' = n
  · rw [dif_pos h]
    constructor
    · intro hh
      have := Option.some.inj hh
      rw [← this]; exact h.choose_spec
    · intro hl
      have hc := h.choose_spec
      have : h.choose = l := Encodable.encode_injective (hc.trans hl.symm)
      rw [this]
  · rw [dif_neg h]
    constructor
    · intro hh; cases hh
    · intro hl; exact absurd ⟨l, hl⟩ h

theorem eOpt_inj (i j : ℕ) (l : whiteBasisIndex) (hi : eOpt i = some l)
    (hj : eOpt j = some l) : i = j := by
  rw [eOpt_eq_some] at hi hj
  rw [← hi, ← hj]

theorem enumerated_eq {V : Type*} [Zero V] (v : whiteBasisIndex → V) (n : ℕ) :
    gaussEnumerated v n = match eOpt n with | some l => v l | none => 0 := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  cases hn : eOpt n with
  | some l =>
    have := (eOpt_eq_some.1 hn)
    rw [← this]
    exact enumerated_encode v l
  | none =>
    have hno : ¬ ∃ l : whiteBasisIndex, Encodable.encode l = n := by
      rintro ⟨l, hl⟩
      have := eOpt_eq_some.2 hl
      rw [hn] at this; cases this
    exact Function.extend_apply' _ _ _ hno

theorem q3Section_scale_fn (β σ : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index) (x y : Vec 2) :
    q3SectionFunction (β / σ) L a x y = σ⁻¹ * q3SectionFunction β L a x y := by
  unfold q3SectionFunction
  ring

theorem conv_scale (β σ : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index) (u : WhiteNoise)
    (x : Vec 2) :
    q3Convolution (β / σ) L a u x = σ⁻¹ * q3Convolution β L a u x := by
  rw [q3Convolution_eq_integral, q3Convolution_eq_integral, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [q3Section_scale_fn]
  ring

theorem hlink'' (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQcl : closure (openCubeSet Q) ⊆ closedRectangle a b c d) (β σ : ℝ)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    (mainQ3DirectionW2 Q (β / σ) L u).value.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => responseCoefficientExtension (physicalResponseRestriction Q hQcl
        (q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L u))) x / σ := by
  have h := ae_restrict_of_forall_mem (μ := volume) (measurableSet_openCubeSet Q)
    (p := fun x => (mainQ3DirectionW2 Q (β / σ) L u).value.toFun x =
      responseCoefficientExtension (physicalResponseRestriction Q hQcl
        (q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L u))) x / σ) (fun x hx => by
    rw [responseCoefficientExtension_eq _ hx]
    have h1 : (mainQ3DirectionW2 Q (β / σ) L u).value.toFun x =
        q3Convolution (β / σ) L h3Zero u x := rfl
    have h2 : physicalResponseRestriction Q hQcl
        (q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L u))
        ⟨x, subset_closure hx⟩ =
        q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L u)
          ⟨x, hQcl (subset_closure hx)⟩ := rfl
    rw [h1, h2, q3H3RangeValue_factor a b c d β hab hcd L u, conv_scale]
    change σ⁻¹ * ⟪u, q3Section β L h3Zero x⟫_ℝ = ⟪u, q3Section β L h3Zero x⟫_ℝ / σ
    ring)
  exact h

end

end ASDExplicitGamma.Scalar
