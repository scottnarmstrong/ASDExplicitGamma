module

public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Inverse.BankDepthObservers
public import ASDExplicitGamma.Inverse.BankDepthHistory
public import ASDExplicitGamma.Inverse.BankInterfaces

/-! Global inverse and scalar observer banks, with only the generator input outstanding. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- The global grouped bank with its causal inverse mean inputs obtained from
the actual pure-flux generator at each earlier label. -/
theorem global_bank_of_states {ι : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (I : Finset ι) (families : ι → Finset (TriadicCube 2)) (hI : I.card ≤ 9^89)
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ i ∈ I, ∀ Q ∈ families i, Q.scale ≤ m ∧ m-Q.scale ≤ 5)
    (hcard : ∀ i ∈ I, (families i).card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    (∀ i ∈ I, InverseBankConclusion M .globalInverse (families i) m J weights) ∧
      eLpNorm (inverseBankGroupedRemainder .globalInverse I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5/10^24:ℝ) ∧
      eLpNorm (inverseBankGroupedHistory I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (14103/10000:ℝ) := by
  exact global_bank M h hM hg I families hI m J hmJ weights hw hscale hcard hpast
    (bank_inverse_mean_inputs_of_states M h hM hg m hpast).1

end ASDExplicitGamma.Inverse
