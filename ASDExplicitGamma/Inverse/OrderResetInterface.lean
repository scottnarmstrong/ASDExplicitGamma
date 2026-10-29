module

public import ASDExplicitGamma.Inverse.OrderBandBounds

/-! Stable source profiles and the interface for the order-reset step.
The theorem displayed below is an intended statement, not a proved declaration.
No result of the unfinished assembly is assumed by this module. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The trace profile at real order p and terminal/reference depths D,f. -/
def orderTraceProfile (γ p D f : ℝ) : ℝ :=
  4*(2+2810*γ*((heightEntrance (orderBand p):ℝ)+20+p*(D+1)))*
    (3:ℝ)^(4*γ*((heightEntrance (orderBand p):ℝ)+20)+2*γ*D+2*γ*f)

/-- The inverse profile with coefficient C=2.07 or C=1.53. -/
def orderInverseProfile (C γ p f : ℝ) : ℝ :=
  C*(3:ℝ)^(2*γ*((heightEntrance (orderBand p):ℝ)+20)+2*γ*f)

/-
Stable intended public producer (proof remains in progress):

theorem q3_order_reset (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N K₀ : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    let m := protectedOldLabel Q.scale (orderBand p)
    let D := ((N-Q.scale+1:ℤ):ℝ)
    let f := |((K₀-Q.scale+1:ℤ):ℝ)|
    eLpNorm (rootTraceObservable M Q m N K₀ weights) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (orderTraceProfile M.gamma p D f) ∧
    eLpNorm (rootInverseObservable M Q m N K₀ weights) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (orderInverseProfile (207/100) M.gamma p f) ∧
    (M.gamma ≤ 1/327680 →
      eLpNorm (rootInverseObservable M Q m N K₀ weights) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (orderInverseProfile (153/100) M.gamma p f))
-/

end
end ASDExplicitGamma.Inverse
