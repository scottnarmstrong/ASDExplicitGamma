module

public import ASDExplicitGamma.Scalar.ResolventAlgebra
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.NoncommRing
public import ASDExplicitGamma.Numerics.Scalar.Lower
public import ASDExplicitGamma.Numerics.Scalar.Frames

/-! Source-level pieces of SC-NEW-RESOLVENT-COMBINE.  The exact averaged
resolvent split and the certified frame-charge arithmetic are available here.
The physical reset-bank flat and defect carriers are not yet defined in Lean,
so this module does not identify them with the numerical certificate inputs. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Matrix MeasureTheory
open ASDExplicitGamma.Numerics.Scalar
open ASDExplicitGamma.Numerics.Mirror

noncomputable section

/-- The exact scalar inequality recorded for SC-NEW-RESOLVENT-FLAT, kept as
a named premise for the fixed physical Wick producer. The carrier value and
NEW-bank split parameters are explicit so a caller must provide this
producer conclusion; the numeric certificate alone does not establish it. -/
def NewResolventFlatConclusion (Fflat : ℝ) : Prop :=
  0 ≤ Fflat ∧
    Fflat ≤ (1557 / 1000 : ℝ) *
      ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ))

/-- The exact variable C-sharp coefficient used by the resolvent combination.
The arguments are the physical flat and defect carriers supplied by the two
component nodes. -/
def newResolventCSharp (Fflat Fdef : ℝ) : ℝ :=
  Fflat + (141 / 50 : ℝ) * Real.sqrt (Fflat * Fdef) +
    (44 / 25 : ℝ) * Fdef

/-- For every source-range exponent, the one-shell geometric increase is
bounded by the exact `x/(1-x)` frame factor. -/
theorem one_shell_ratio_bounds (gamma : ℝ) (hgamma : 0 < gamma)
    (hgammaMax : gamma ≤ 17 / 50000) :
    let x := (11 / 5 : ℝ) * gamma
    0 ≤ x ∧ x < 1 ∧ (3 : ℝ) ^ (2 * gamma) - 1 ≤ x / (1 - x) := by
  dsimp only
  have hx0 : 0 ≤ (11 / 5 : ℝ) * gamma := by positivity
  have hxmax : (11 / 5 : ℝ) * gamma ≤ (11 / 5) * (17 / 50000) :=
    mul_le_mul_of_nonneg_left hgammaMax (by norm_num)
  have hxlt : (11 / 5 : ℝ) * gamma < 1 := by
    have hbound : (11 / 5 : ℝ) * (17 / 50000) < 1 := by norm_num
    exact hxmax.trans_lt hbound
  have hpow := three_power_le_geometric (2 * gamma) (by linarith) (by
    nlinarith only [hxlt])
  refine ⟨hx0, hxlt, ?_⟩
  have hden : 0 < 1 - (11 / 5 : ℝ) * gamma := by linarith
  have := hpow
  change (3 : ℝ) ^ (2 * gamma) ≤
    1 / (1 - (11 / 10 : ℝ) * (2 * gamma)) at this
  have hdenEq : (1 - (11 / 10 : ℝ) * (2 * gamma)) =
      1 - (11 / 5 : ℝ) * gamma := by ring
  rw [hdenEq] at this
  have hratio : (3 : ℝ) ^ (2 * gamma) ≤ 1 / (1 - (11 / 5 : ℝ) * gamma) := this
  calc
    (3 : ℝ) ^ (2 * gamma) - 1 ≤
        1 / (1 - (11 / 5 : ℝ) * gamma) - 1 := by linarith
    _ = ((11 / 5 : ℝ) * gamma) / (1 - (11 / 5 : ℝ) * gamma) := by
      have hden5 : (5 : ℝ) - 11 * gamma ≠ 0 := by nlinarith [hden]
      field_simp [hden.ne', hden5]
      ring

/-- The source flat conclusion combines with the exact defect-node output by
the Cauchy cross term. This is the real SC-NEW-RESOLVENT-COMBINE consumer
inequality, with only the two named physical component bounds as inputs. -/
theorem new_resolvent_combine_of_component_bounds
    (Fflat Fdef FdefCap : ℝ)
    (hflat : NewResolventFlatConclusion Fflat)
    (hdef0 : 0 ≤ Fdef) (hdef : Fdef ≤ FdefCap) :
    Fflat + (141 / 50 : ℝ) * Real.sqrt (Fflat * Fdef) +
        (44 / 25 : ℝ) * Fdef ≤
      (1557 / 1000 : ℝ) *
          ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) +
        (141 / 50 : ℝ) * Real.sqrt
          ((1557 / 1000 : ℝ) *
            ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) * FdefCap) +
        (44 / 25 : ℝ) * FdefCap := by
  rcases hflat with ⟨hflat0, hflatCap⟩
  have hflatCap0 : 0 ≤ (1557 / 1000 : ℝ) *
      ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) := by
    norm_num
  have hprod : Fflat * Fdef ≤
      ((1557 / 1000 : ℝ) *
        ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ))) *
          FdefCap :=
    mul_le_mul hflatCap hdef hdef0 hflatCap0
  have hsqrt := Real.sqrt_le_sqrt hprod
  have hD1 : 0 ≤ (141 / 50 : ℝ) := by norm_num
  have hD2 : 0 ≤ (44 / 25 : ℝ) := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hsqrt hD1,
    mul_le_mul_of_nonneg_left hflatCap hD1,
    mul_le_mul_of_nonneg_left hdef hD2]

/-- The source frame factor converts the C-sharp coefficient into the paid
one-shell charge for every allowed gamma. This theorem keeps the actual
component carriers symbolic; the flat and defect nodes supply their bounds. -/
theorem new_resolvent_combine_paid_charge_of_component_bounds
    (gamma Fflat Fdef FdefCap : ℝ)
    (hgamma : 0 < gamma) (hgammaMax : gamma ≤ 17 / 50000)
    (hflat : NewResolventFlatConclusion Fflat)
    (hdef0 : 0 ≤ Fdef) (hdef : Fdef ≤ FdefCap) :
    newResolventCSharp Fflat Fdef * ((3 : ℝ) ^ (2 * gamma) - 1) ≤
      ( (1557 / 1000 : ℝ) *
          ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) +
        (141 / 50 : ℝ) * Real.sqrt
          ((1557 / 1000 : ℝ) *
            ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) *
            FdefCap) +
        (44 / 25 : ℝ) * FdefCap) *
        (((11 / 5 : ℝ) * gamma) / (1 - (11 / 5 : ℝ) * gamma)) := by
  have hflat0 := hflat.1
  rcases hflat with ⟨_, hflatCap⟩
  have hcap0 : 0 ≤ (1557 / 1000 : ℝ) *
      ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) := by
    norm_num
  have hcapDef0 : 0 ≤ FdefCap := le_trans hdef0 hdef
  have hratio := one_shell_ratio_bounds gamma hgamma hgammaMax
  have hratio0 : 0 ≤ ((11 / 5 : ℝ) * gamma) /
      (1 - (11 / 5 : ℝ) * gamma) := by
    exact div_nonneg (by positivity) (by linarith [hratio.2.1])
  have hC : newResolventCSharp Fflat Fdef ≤
      (1557 / 1000 : ℝ) *
          ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) +
        (141 / 50 : ℝ) * Real.sqrt
          ((1557 / 1000 : ℝ) *
            ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10^24 : ℝ)) *
            FdefCap) +
        (44 / 25 : ℝ) * FdefCap := by
    simpa [newResolventCSharp] using
      new_resolvent_combine_of_component_bounds
        Fflat Fdef FdefCap ⟨hflat0, hflatCap⟩ hdef0 hdef
  have hC0 : 0 ≤ newResolventCSharp Fflat Fdef := by
    have hsqrt0 : 0 ≤ Real.sqrt (Fflat * Fdef) := Real.sqrt_nonneg _
    dsimp [newResolventCSharp]
    positivity
  have hratioMul := mul_le_mul_of_nonneg_left hratio.2.2 hC0
  have hcapMul := mul_le_mul_of_nonneg_right hC hratio0
  calc
    newResolventCSharp Fflat Fdef * ((3 : ℝ) ^ (2 * gamma) - 1) ≤
        newResolventCSharp Fflat Fdef *
          (((11 / 5 : ℝ) * gamma) / (1 - (11 / 5 : ℝ) * gamma)) := hratioMul
    _ ≤ _ := hcapMul

end
end ASDExplicitGamma.Scalar
