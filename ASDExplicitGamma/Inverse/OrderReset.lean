module

public import ASDExplicitGamma.Inverse.AssemblyTraceProfileLp
public import ASDExplicitGamma.Inverse.AssemblyInverseProfile

/-! Proved all-order producers, packaged at the stable order-reset interface. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The positive trace and inverse estimates at every real order and every
reference frame, with the conditional small-gamma coefficient. -/
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
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (orderInverseProfile (153/100) M.gamma p f)) := by
  let m := protectedOldLabel Q.scale (orderBand p)
  let D := ((N-Q.scale+1:ℤ):ℝ)
  let f := |((K₀-Q.scale+1:ℤ):ℝ)|
  have htrace := assembly_root_trace_profile_Lp M h hM hγ Q p hp hpast N K₀ hN weights hw
  have hinverse := assembly_reference_inverse_profile_Lp M h hM hγ Q p hp hpast
    N K₀ hN weights hw
  have hbase : 0 ≤ (3:ℝ)^(2*M.gamma*
      ((heightEntrance (orderBand p):ℝ)+20)+
        2*M.gamma*|((K₀-Q.scale+1:ℤ):ℝ)|) := by positivity
  have hcoeff : (153/100:ℝ) ≤ 207/100 := by norm_num
  have hInv207 : eLpNorm (rootInverseObservable M Q m N K₀ weights)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (orderInverseProfile (207/100) M.gamma p f) := by
    apply le_trans hinverse
    apply ENNReal.ofReal_le_ofReal
    dsimp [orderInverseProfile]
    exact mul_le_mul_of_nonneg_right hcoeff hbase
  refine ⟨?_,hInv207,?_⟩
  · simpa only [m,D,f] using htrace
  · intro _
    simpa only [m,f,orderInverseProfile] using hinverse

end
end ASDExplicitGamma.Inverse
