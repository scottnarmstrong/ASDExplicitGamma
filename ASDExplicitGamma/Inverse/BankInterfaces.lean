module

public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Inverse.BankGrouping

/-! Source first-local, global and OLD-local observer-bank interfaces. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- First-local ordinary and scalar-grouped banks, with the actual source
reserve 3*10^-46 and its separate five-fold grouping reserve. -/
theorem first_local_bank_grouped {ι : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (I : Finset ι) (families : ι → Finset (TriadicCube 2)) (hI : I.card ≤ 9^89)
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ i ∈ I, ∀ Q ∈ families i, Q.scale ≤ m ∧ m-Q.scale ≤ 5)
    (hcard : ∀ i ∈ I, (families i).card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    (∀ i ∈ I, InverseBankConclusion M .firstLocal (families i) m J weights) ∧
      eLpNorm (inverseBankGroupedRemainder .firstLocal I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (15/10^46:ℝ) ∧
      eLpNorm (inverseBankGroupedHistory I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (159/100:ℝ) := by
  have hmean := clipped_inverse_mean_input_first_full M h hg m .firstLocal (Or.inl rfl) hpast
  have hh := inverse_bank_grouped M h hM hg .firstLocal I families hI m J hmJ weights hw
    hscale hcard hpast hmean
  refine ⟨fun i hi => first_local_inverse_bank M h hM hg _ m J hmJ weights hw
    (hscale i hi) (hcard i hi) hpast, ?_, ?_⟩
  · have heq : (5*(inverseBankReserve .firstLocal:ℝ)) = (15/10^46:ℝ) := by
      norm_num [inverseBankReserve]
    exact heq ▸ hh.2.1
  · simpa [inverseBankCap] using hh.2.2

/-- Part B global bank: the ordinary 10^-24 reserve and scalar-grouped
5*10^-24 reserve retain the separately proved total 1.4103 cap. -/
theorem global_bank {ι : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (I : Finset ι) (families : ι → Finset (TriadicCube 2)) (hI : I.card ≤ 9^89)
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ i ∈ I, ∀ Q ∈ families i, Q.scale ≤ m ∧ m-Q.scale ≤ 5)
    (hcard : ∀ i ∈ I, (families i).card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m .globalInverse) :
    (∀ i ∈ I, InverseBankConclusion M .globalInverse (families i) m J weights) ∧
      eLpNorm (inverseBankGroupedRemainder .globalInverse I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5/10^24:ℝ) ∧
      eLpNorm (inverseBankGroupedHistory I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (14103/10000:ℝ) := by
  have hh := inverse_bank_grouped M h hM hg .globalInverse I families hI m J hmJ weights hw
    hscale hcard hpast hmean
  refine ⟨fun i hi => global_inverse_bank M h hM hg _ m J hmJ weights hw
    (hscale i hi) (hcard i hi) hpast hmean, ?_, ?_⟩
  · have heq : (5*(inverseBankReserve .globalInverse:ℝ)) = (5/10^24:ℝ) := by
      norm_num [inverseBankReserve]
    exact heq ▸ hh.2.1
  · simpa [inverseBankCap] using hh.2.2

/-- Part B OLD local bank, keeping its 3*10^-46 ordinary and 1.5*10^-45
grouped reserves distinct from the global reserve. -/
theorem local_bank {ι : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (I : Finset ι) (families : ι → Finset (TriadicCube 2)) (hI : I.card ≤ 9^89)
    (m J : ℤ) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ i ∈ I, ∀ Q ∈ families i, Q.scale ≤ m ∧ m-Q.scale ≤ 5)
    (hcard : ∀ i ∈ I, (families i).card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m .localInverse) :
    (∀ i ∈ I, InverseBankConclusion M .localInverse (families i) m J weights) ∧
      eLpNorm (inverseBankGroupedRemainder .localInverse I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (15/10^46:ℝ) ∧
      eLpNorm (inverseBankGroupedHistory I families M m J weights) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3683/2500:ℝ) := by
  have hh := inverse_bank_grouped M h hM hg .localInverse I families hI m J hmJ weights hw
    hscale hcard hpast hmean
  refine ⟨fun i hi => local_inverse_bank M h hM hg _ m J hmJ weights hw
    (hscale i hi) (hcard i hi) hpast hmean, ?_, ?_⟩
  · have heq : (5*(inverseBankReserve .localInverse:ℝ)) = (15/10^46:ℝ) := by
      norm_num [inverseBankReserve]
    exact heq ▸ hh.2.1
  · simpa [inverseBankCap] using hh.2.2

end ASDExplicitGamma.Inverse
