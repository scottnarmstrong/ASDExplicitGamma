/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.Profile
public import ASDExplicitGamma.Inverse.OrderReset

/-! # Profile nodes from the order reset -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- Instantiate the exact reset interface with the source theorem. -/
theorem order_reset_producer : OrderResetProducer := by
  intro M h hM hγ Q p hp hpast N K₀ hN weights hw
  exact Inverse.q3_order_reset M h hM hγ Q p hp hpast N K₀ hN weights hw

/-- AO-ALL-PROFILE from the order reset.  The
conclusion is the exact real profile interface consumed by the CIR and
per-depth assemblies. -/
theorem ao_all_profile
    (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * Inverse.orderBand p → nativeInductionState M h n)
    (N K₀ : ℤ) (hN : Q.scale - 1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc
      (Inverse.protectedOldLabel Q.scale (Inverse.orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    orderResetProfileConclusion M Q p N K₀ weights := by
  exact ao_all_profile_of_order_reset order_reset_producer
    M h hM hγ Q p hp hpast N K₀ hN weights hw

end ASDExplicitGamma.AllOrder
