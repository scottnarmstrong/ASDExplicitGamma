module

public import ASDExplicitGamma.Inverse.BankGlobal

/-! The OLD local inverse and scalar banks retain their distinct source reserves. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- OLD local bank for both physical endpoints and every deterministic attenuation,
including the source union of refinements and the depth extensions. -/
theorem local_inverse_bank_attenuated_of_generator
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (hQ : Q.scale=m+40) (rmax : ℕ) (hr : rmax ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpast : ∀ n < m, nativeInductionState M h n)
    (hgen : ∀ n < m, BankPureFluxGeneratorInput M h (n-40)) :
    InverseBankConclusion M .localInverse (bankObserverRootUnion Q rmax) m (m+40)
        (bankPartialInsertionWeights m 1 t) ∧
      (∀ j : ℕ,
        InverseBankDepthConclusion M .localInverse (bankObserverDepthRootUnion Q rmax j)
          m (m+40) (bankPartialInsertionWeights m 1 t) j ∧
        InverseBankDepthBlockConclusion M .localInverse (bankObserverDepthRootUnion Q rmax j)
          m (m+40) (bankPartialInsertionWeights m 1 t) j) := by
  have hmean := (bank_inverse_mean_inputs_of_generator M h hM hg m hpast hgen).2
  have hw : ∀ i ∈ Finset.Ioc m (m+40), 0 ≤ bankPartialInsertionWeights m 1 t i ∧
      bankPartialInsertionWeights m 1 t i ≤ 1 :=
    fun i _ => bank_partial_insertion_weights_bounds m 1 t ht.2 i
  have hgeometry := bank_observer_union_geometry Q m hQ rmax hr
  exact ⟨local_inverse_bank M h hM hg _ m (m+40) (by omega) _ hw
    hgeometry.1 hgeometry.2 hpast hmean,
    inverse_bank_observer_union_depths M h hM hg .localInverse Q m (m+40) hQ (by omega)
      _ hw rmax hr hpast hmean⟩

/-- The OLD local inverse bank with its one-pass mean input filled by the
pure-flux generator at every strictly earlier completed label. -/
theorem local_inverse_bank_attenuated_of_states
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (m : ℤ) (hQ : Q.scale=m+40) (rmax : ℕ) (hr : rmax ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    InverseBankConclusion M .localInverse (bankObserverRootUnion Q rmax) m (m+40)
        (bankPartialInsertionWeights m 1 t) ∧
      (∀ j : ℕ,
        InverseBankDepthConclusion M .localInverse (bankObserverDepthRootUnion Q rmax j)
          m (m+40) (bankPartialInsertionWeights m 1 t) j ∧
        InverseBankDepthBlockConclusion M .localInverse (bankObserverDepthRootUnion Q rmax j)
          m (m+40) (bankPartialInsertionWeights m 1 t) j) := by
  apply local_inverse_bank_attenuated_of_generator M h hM hg Q m hQ rmax hr t ht hpast
  intro n hn
  exact bankPureFluxGeneratorInput M h hM hg (n-40) (fun j hj => hpast j (by omega))

end ASDExplicitGamma.Inverse
