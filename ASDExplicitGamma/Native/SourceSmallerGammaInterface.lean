module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.CompletedPrefixEndpoint

/-! Completed-law consumer interface for the native smaller-gamma source
chain. Extended nonnegative integrals retain all possible infinite values. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- Actual completed source mean at depth r, in the true completed frame.
The coefficient cutoff remains m at every depth. -/
def nativeCompletedSourceMean (M : ABKModel 2) (m : ℤ) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (cutoffTraceDefect M m (m-(r:ℤ)) ω)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The actual completed weak-row charge: its deterministic OLD inverse
baseline times the actual mean, plus the marginal rare payment times the
actual L20 trace. This is the bound of that row. A simultaneous maximum inverse-depth
proxy additionally needs the separate mixed-bridge reserve; it is not this row.
The ENNReal depth series retains every tail and any infinite moment. -/
def nativeCompletedSourceWeak (M : ABKModel 2) (m : ℤ) (r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1-Scalar.inverseHistoryDiscount^2)*
    ∑' j : ℕ, ENNReal.ofReal (Scalar.inverseHistoryDiscount^(2*j)*(3:ℝ)^(2*M.gamma*(j:ℝ)))*
      (ENNReal.ofReal (3683/2500:ℝ)*nativeCompletedSourceMean M m (r+j)+
        ENNReal.ofReal (3/10^46:ℝ)*eLpNorm (cutoffTraceDefect M m (m-((r+j:ℕ):ℤ))) 20
          (Cutoff.cutoffSampleLaw M).toMeasure)

/-- Exact corrected q1 endpoint, kept separate from the legacy Q-star. -/
def nativeBoundaryQ1Sharp : ℚ :=
  1095712671923674591833653217481626040963161/(15625*10^39)

/-- Conclusion of the smaller-gamma chain. The six weak rows
bound the actual-law baseline and marginal rare charge, including the complete depth series.
The tighter corrected parent endpoints imply the carried legacy endpoints. -/
structure NativeSourceSmallerGammaBounds (M : ABKModel 2) (m : ℤ) : Prop where
  q1 : nativeCompletedSourceMean M m 1 ≤ ENNReal.ofReal (theta M*(nativeBoundaryQ1Sharp:ℝ))
  parent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
    ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ))
  mean : ∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
    ENNReal.ofReal (theta M*((nativeCompletedMeanRows.getD r.val 0:ℚ):ℝ))
  weak : ∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
    ENNReal.ofReal (theta M*((nativeCompletedWeakRows.getD r.val 0:ℚ):ℝ))

/-- Depth zero is exactly the frozen ordinary-mean coordinate, without a
finite-toReal convention. -/
theorem native_completed_source_mean_zero (M : ABKModel 2) (m : ℤ) :
    nativeCompletedSourceMean M m 0=ordinaryMean M m := by
  simp only [nativeCompletedSourceMean,Nat.cast_zero,sub_zero,ordinaryMean]

end
end ASDExplicitGamma.Native
