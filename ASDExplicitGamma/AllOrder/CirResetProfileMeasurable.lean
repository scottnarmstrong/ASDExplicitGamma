/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenHistoryProfile
public import ASDExplicitGamma.AllOrder.CirResetHistoryBridge

/-! # Measurable reset inverse maxima and profile series -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Inverse
open Homogenization.Book

namespace ASDExplicitGamma.AllOrder

/-- Every real-order reset estimate controls one fixed measurable series
envelope; only the proof's protected-label order varies. -/
theorem aoCir_reset_inverse_fixed_envelope_bound
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hγsmall : M.gamma ≤ 1 / 327680)
    (hstate : ∀ n : ℤ, nativeInductionState M h n)
    (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hQN : Q.scale ≤ N) (j : ℕ) (q : ℝ) (hq48 : 48 ≤ q)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (aoCirResetInverseDepthProfileSeries M Q j N 48 t)
        (ENNReal.ofReal q) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (aoCirInverseHistoryFactor M.gamma *
        Real.rpow 9 ((j : ℝ) / q) *
        orderInverseProfile (153 / 100) M.gamma q ((j : ℝ) + 1)) := by
  have hbound := aoCir_reset_inverse_depth_profile_series_bound reset M h hM hγ
    hγsmall hstate Q N hQN j q hq48 t ht0 ht1
  have heq : aoCirResetInverseDepthProfileSeries M Q j N 48 t =
      aoCirResetInverseDepthProfileSeries M Q j N q t := by
    funext ω
    exact aoCir_reset_inverse_depth_profile_series_order_independent
      M Q n ell hQ hK N hQN j 48 q t ω
  rw [heq]
  exact hbound

end ASDExplicitGamma.AllOrder
