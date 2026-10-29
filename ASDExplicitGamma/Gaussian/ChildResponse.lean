module

public import ASDExplicitGamma.Gaussian.PolynomialTests
public import ASDExplicitGamma.Gaussian.GaussCentering

/-! # The literal child response test W_r (8.16) -/

@[expose] public section

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
open MeasureTheory

namespace ASDExplicitGamma.Gaussian

/-- The child trace response (1.8), defined by the same four affine variational minima.
The scalar coefficient is physical: ν is its symmetric part and σ is only the frame. -/
noncomputable def childTraceObservable {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] [CompactSpace (closure U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) : C(closure U, ℝ) → ℝ := fun k =>
  (∑ i : Fin 2,
    (responseFrameEnergyObservable hU hvol ν σ hν hσ (orthonormalFrameLoad i 1)
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k) +
    responseFrameEnergyObservable hU hvol ν σ hν hσ (orthonormalFrameLoad i (-1))
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k))) - 4

theorem childTraceObservable_polynomial {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] [CompactSpace (closure U)]
    (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    HasPolynomiallyBoundedC2Derivatives (childTraceObservable hU hvol ν σ hν hσ) := by
  let L := (ContinuousMap.linearIsometryBoundedOfCompact (closure U) ℝ ℝ).toLinearIsometry
  let E (i : Fin 2) (r : ℝ) := fun k => responseFrameEnergyObservable hU hvol ν σ hν hσ
    (orthonormalFrameLoad i r) (L k)
  have hE (i : Fin 2) (r : ℝ) : HasPolynomiallyBoundedC2Derivatives (E i r) :=
    hasPolynomiallyBoundedC2Derivatives_comp_isometry L
      (responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives hU hvol ν σ hν hσ (orthonormalFrameLoad i r))
  have hsum : HasPolynomiallyBoundedC2Derivatives (fun k => ∑ i : Fin 2, (E i 1 k + E i (-1) k)) :=
    c2_polynomial_sum Finset.univ _ (fun i hi => hasPolynomiallyBoundedC2Derivatives_add (hE i 1) (hE i (-1)))
  exact hasPolynomiallyBoundedC2Derivatives_sub_const hsum 4

section Children
variable {n : ℕ} (U : Fin n → Set (Vec 2))
  [∀ i, IsFiniteMeasure (volumeMeasureOn (U i))] [∀ i, CompactSpace (closure (U i))]
  (hU : ∀ i, MeasurableSet (U i)) (hvol : ∀ i, 0 < (volume (U i)).toReal)
  (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)

/-- The averaged physical child trace in a product coefficient space. -/
noncomputable def childMeanTrace [NeZero n] (k : ∀ i, C(closure (U i), ℝ)) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i)

/-- The finite normalized mean of the child traces retains polynomial C²
control, before taking any natural power. -/
theorem childMeanTrace_polynomial [NeZero n] :
    HasPolynomiallyBoundedC2Derivatives (childMeanTrace U hU hvol ν σ hν hσ) := by
  have hc (i : Fin n) : HasPolynomiallyBoundedC2Derivatives
      (fun k : ∀ i, C(closure (U i), ℝ) =>
        childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i)) :=
    c2_polynomial_component (F := fun i => C(closure (U i), ℝ)) i
      (childTraceObservable_polynomial (hU i) (hvol i) ν σ hν hσ)
  have hs : HasPolynomiallyBoundedC2Derivatives
      (fun k : ∀ i, C(closure (U i), ℝ) => ∑ i : Fin n,
        childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i)) :=
    c2_polynomial_sum (Finset.univ : Finset (Fin n))
      (fun i (k : ∀ i, C(closure (U i), ℝ)) =>
        childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i))
      (fun i hi => hc i)
  change HasPolynomiallyBoundedC2Derivatives
    (fun k : ∀ i, C(closure (U i), ℝ) =>
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i))
  exact c2_polynomial_mul
    (c2_polynomial_const (E := (∀ i, C(closure (U i), ℝ))) (n : ℝ)⁻¹) hs

/-- The power test before separate child constant shifts. -/
noncomputable def childPower [NeZero n] (r : ℕ) (k : ∀ i, C(closure (U i), ℝ)) : ℝ :=
  (childMeanTrace U hU hvol ν σ hν hσ k) ^ r

/-- Separate constant fields need not patch to a global continuous coefficient. -/
noncomputable def childW [NeZero n] (r : ℕ) (k : ∀ i, C(closure (U i), ℝ)) (g : Fin n → ℝ) : ℝ :=
  childPower U hU hvol ν σ hν hσ r (k + childConstantMap (fun i => closure (U i)) g)

theorem childPower_polynomial [NeZero n] (r : ℕ) :
    HasPolynomiallyBoundedC2Derivatives (childPower U hU hvol ν σ hν hσ r) := by
  have hc (i : Fin n) : HasPolynomiallyBoundedC2Derivatives
      (fun k : ∀ i, C(closure (U i), ℝ) => childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i)) :=
    c2_polynomial_component (F := fun i => C(closure (U i), ℝ)) i
      (childTraceObservable_polynomial (hU i) (hvol i) ν σ hν hσ)
  have hs : HasPolynomiallyBoundedC2Derivatives
      (fun k : ∀ i, C(closure (U i), ℝ) => ∑ i : Fin n,
        childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i)) :=
    c2_polynomial_sum (Finset.univ : Finset (Fin n))
      (fun i (k : ∀ i, C(closure (U i), ℝ)) =>
        childTraceObservable (hU i) (hvol i) ν σ hν hσ (k i)) (fun i hi => hc i)
  exact c2_polynomial_pow (c2_polynomial_mul (c2_polynomial_const (E := (∀ i, C(closure (U i), ℝ))) (n : ℝ)⁻¹) hs) r

end Children
end ASDExplicitGamma.Gaussian
