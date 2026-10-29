module

public import ASDExplicitGamma.Numerics.MainReturnCertificate.Formula
public import ASDExplicitGamma.Numerics.Mirror.GridThree
import Mathlib.Tactic.NormNum

/-!
# Kernel checks for the fields used by the main-return recurrence

The generated endpoints are integers in units of `10^32`. This module checks the exponential
and frame fields against the Mirror enclosures, and states their meanings over `ℝ`.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.MainReturnCertificate

open ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.Mirror
open ASDExplicitGamma.Numerics.Spike

/-- The rational decay exponent computed from a panel's certified lower slope. -/
def panelDecayArgument (e : PanelEndpoints) : ℚ :=
  -((e.ellLower : ℚ) / (8 * (Spike.gridScale : ℚ)))

/-- Decide the panel recurrence-field comparisons using the Mirror's exponential enclosure. -/
def panelRecurrenceFieldGridCheck (e : PanelEndpoints) : Bool := decide
  (0 < e.ellLower ∧
    e.ellLower ≤ e.supportLambdaLower ∧
    e.rhoLower ≤ Spike.gridScale ∧
    (-50 : ℚ) ≤ panelDecayArgument e ∧
    panelDecayArgument e ≤ 50 ∧
    (e.rhoLower : ℚ) / (Spike.gridScale : ℚ) ≤
      expPointLower mainReturnGridDigits mainReturnTaylorDegree (panelDecayArgument e) ∧
    expPointUpper mainReturnGridDigits mainReturnTaylorDegree (panelDecayArgument e) ≤
      (e.rhoUpper : ℚ) / (Spike.gridScale : ℚ) ∧
    e.offsetUpper * e.ellLower ≥ e.aUpper * (Spike.gridScale - e.rhoLower))

/-- Real-valued panel fields consumed by `Spike.advancePanel`. All integer endpoints are
interpreted in grid units; the last inequality is the exact cross-multiplied offset bound. -/
def panelRecurrenceFields (e : PanelEndpoints) : Prop :=
  0 < (e.ellLower : ℝ) ∧
    (e.ellLower : ℝ) ≤ (e.supportLambdaLower : ℝ) ∧
    0 ≤ (e.aUpper : ℝ) ∧
    (e.rhoLower : ℝ) / (Spike.gridScale : ℝ) ≤
      Real.exp (-(e.ellLower : ℝ) / (8 * (Spike.gridScale : ℝ))) ∧
    Real.exp (-(e.ellLower : ℝ) / (8 * (Spike.gridScale : ℝ))) ≤
      (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) ∧
    (e.offsetUpper : ℝ) * (e.ellLower : ℝ) ≥
      (e.aUpper : ℝ) * ((Spike.gridScale : ℝ) - (e.rhoLower : ℝ))

/-- A successful grid check proves all real-valued panel recurrence-field bounds. -/
theorem panelRecurrenceFields_sound (e : PanelEndpoints)
    (hcheck : panelRecurrenceFieldGridCheck e = true) : panelRecurrenceFields e := by
  have hc := of_decide_eq_true hcheck
  rcases hc with ⟨hellpos, hell, hrho, hqlo, hqhi, hrlo, hrhi, hoff⟩
  have hExp := expPoint_bounds mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge hqlo hqhi
  have harg : (panelDecayArgument e : ℝ) =
      -(e.ellLower : ℝ) / (8 * (Spike.gridScale : ℝ)) := by
    norm_num [panelDecayArgument, Spike.gridScale]
    ring
  rw [harg] at hExp
  have hrloR : (((e.rhoLower : ℚ) / (Spike.gridScale : ℚ) : ℚ) : ℝ) ≤
      (expPointLower mainReturnGridDigits mainReturnTaylorDegree
        (panelDecayArgument e) : ℝ) := by exact_mod_cast hrlo
  have hRhoLowerCast : (((e.rhoLower : ℚ) / (Spike.gridScale : ℚ) : ℚ) : ℝ) =
      (e.rhoLower : ℝ) / (Spike.gridScale : ℝ) := by
    norm_num
  rw [hRhoLowerCast] at hrloR
  have hrhiR : (expPointUpper mainReturnGridDigits mainReturnTaylorDegree
      (panelDecayArgument e) : ℝ) ≤
      (((e.rhoUpper : ℚ) / (Spike.gridScale : ℚ) : ℚ) : ℝ) := by exact_mod_cast hrhi
  have hRhoUpperCast : (((e.rhoUpper : ℚ) / (Spike.gridScale : ℚ) : ℚ) : ℝ) =
      (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) := by
    norm_num
  rw [hRhoUpperCast] at hrhiR
  have hoff' : ((e.offsetUpper * e.ellLower : ℕ) : ℝ) ≥
      ((e.aUpper * (Spike.gridScale - e.rhoLower) : ℕ) : ℝ) := by
    exact_mod_cast hoff
  have hoff'' : (e.offsetUpper : ℝ) * (e.ellLower : ℝ) ≥
      (e.aUpper : ℝ) * ((Spike.gridScale : ℝ) - (e.rhoLower : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hrho] at hoff'
    exact hoff'
  exact ⟨by exact_mod_cast hellpos, by exact_mod_cast hell,
    by positivity, hrloR.trans hExp.1, hExp.2.trans hrhiR, hoff''⟩

/-- The exact exponent used by every insertion frame: `2 * γ₀` with `γ₀ = 17/50000`. -/
def mainReturnFrameExponent : ℚ := 2 * (17 / 50000)

/-- Exact rational exponent input for the Mirror's three-power enclosure. -/
def mainReturnFrameInput : QInterval :=
  ⟨mainReturnFrameExponent, mainReturnFrameExponent, le_rfl⟩

/-- The exponent-times-`log 3` interval lies within the Mirror exponential range. -/
theorem mainReturnFrameArgumentBounds :
    -50 ≤ (Mirror.mul mainReturnGridDigits mainReturnFrameInput
        (logThree mainReturnGridDigits)).lo ∧
      (Mirror.mul mainReturnGridDigits mainReturnFrameInput
        (logThree mainReturnGridDigits)).hi ≤ 50 := by
  norm_num [Mirror.mul, Mirror.logThree, Mirror.round, Mirror.roundDown,
    Mirror.roundUp, Mirror.gridScale,
    logThreeRaw, QInterval.mul, mainReturnFrameInput, mainReturnFrameExponent,
    mainReturnGridDigits]

/-- Outward Mirror enclosure of the insertion multiplier `3^(2γ₀)`. -/
def mainReturnFramePower : QInterval :=
  powThree mainReturnGridDigits mainReturnTaylorDegree mainReturnFrameInput
    mainReturnTaylorDegree_ge mainReturnFrameArgumentBounds.1
      mainReturnFrameArgumentBounds.2

/-- The Mirror three-power interval contains the exact insertion frame factor. -/
theorem mainReturnFramePower_sound :
    QInterval.Contains mainReturnFramePower
      ((3 : ℝ) ^ ((mainReturnFrameExponent : ℚ) : ℝ)) := by
  have hexp := powThree_sound mainReturnGridDigits mainReturnTaylorDegree
    mainReturnTaylorDegree_ge mainReturnFrameArgumentBounds.1
      mainReturnFrameArgumentBounds.2
      (x := ((mainReturnFrameExponent : ℚ) : ℝ))
      (by
        change (mainReturnFrameInput.lo : ℝ) ≤ (mainReturnFrameExponent : ℝ) ∧
          (mainReturnFrameExponent : ℝ) ≤ mainReturnFrameInput.hi
        simp [mainReturnFrameInput])
  simpa [mainReturnFramePower] using hexp

/-- Decide whether the stored insertion frame endpoints enclose the Mirror three-power interval. -/
def insertionFrameRecurrenceFieldGridCheck (frameLower frameUpper : ℕ) : Bool := decide
  ((frameLower : ℚ) / (Spike.gridScale : ℚ) ≤ mainReturnFramePower.lo ∧
    mainReturnFramePower.hi ≤ (frameUpper : ℚ) / (Spike.gridScale : ℚ))

/-- Real-valued frame enclosure for one insertion, with exponent `2γ₀`. -/
def insertionFrameRecurrenceFields (frameLower frameUpper : ℕ) : Prop :=
  (frameLower : ℝ) / (Spike.gridScale : ℝ) ≤
      (3 : ℝ) ^ ((mainReturnFrameExponent : ℚ) : ℝ) ∧
    (3 : ℝ) ^ ((mainReturnFrameExponent : ℚ) : ℝ) ≤
      (frameUpper : ℝ) / (Spike.gridScale : ℝ)

/-- A successful grid check proves the insertion's real-valued frame enclosure. -/
theorem insertionFrameRecurrenceFields_sound (frameLower frameUpper : ℕ)
    (hcheck : insertionFrameRecurrenceFieldGridCheck frameLower frameUpper = true) :
    insertionFrameRecurrenceFields frameLower frameUpper := by
  have hc := of_decide_eq_true hcheck
  have hpow := mainReturnFramePower_sound
  have hloQ : ((frameLower : ℚ) / (Spike.gridScale : ℚ) : ℝ) ≤
      (mainReturnFramePower.lo : ℝ) := by exact_mod_cast hc.1
  have hhiQ : (mainReturnFramePower.hi : ℝ) ≤
      ((frameUpper : ℚ) / (Spike.gridScale : ℚ) : ℝ) := by exact_mod_cast hc.2
  have hloCast : ((frameLower : ℚ) / (Spike.gridScale : ℚ) : ℝ) =
      (frameLower : ℝ) / (Spike.gridScale : ℝ) := by
    norm_num [Spike.gridScale]
  have hhiCast : ((frameUpper : ℚ) / (Spike.gridScale : ℚ) : ℝ) =
      (frameUpper : ℝ) / (Spike.gridScale : ℝ) := by
    norm_num [Spike.gridScale]
  rw [hloCast] at hloQ
  rw [hhiCast] at hhiQ
  have hlo := hloQ
  have hhi := hhiQ
  exact ⟨hlo.trans hpow.1, hpow.2.trans hhi⟩

end ASDExplicitGamma.Numerics.MainReturnCertificate
