module

public import ASDExplicitGamma.Inverse.BankGlobal

/-! The scalar 9^89 grouping on the actual Q_(m+129) parent. Only the rare
reserve is multiplied by five; the ordinary bank and total cap are distinct. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

/-- Exactly the 9^89 macrocells of side 3^(m+40) inside the scalar parent. -/
def oldHessianMacroCells (m : ℤ) : Finset (TriadicCube 2) :=
  descendantsAtDepth (originCube 2 (m+129)) 89

/-- The scalar parent has precisely the allowed grouping population, and
every macrocell supports the original six-level observer family. -/
theorem old_hessian_macrocell_geometry (m : ℤ) :
    (oldHessianMacroCells m).card = 9^89 ∧
    ∀ Q ∈ oldHessianMacroCells m,
      Q.scale=m+40 ∧
      (∀ U ∈ bankObserverRootUnion Q 5,U.scale≤m ∧ m-U.scale≤5) ∧
      (bankObserverRootUnion Q 5).card≤6*9^45 := by
  refine ⟨?_,?_⟩
  · rw [oldHessianMacroCells,descendantsAtDepth_card]
    norm_num
  · intro Q hQ
    have hscale : Q.scale=m+40 := by
      have hh := scale_eq_sub_of_mem_descendantsAtDepth hQ
      change Q.scale=m+129-(89:ℕ) at hh
      omega
    exact ⟨hscale,bank_observer_union_geometry Q m hscale 5 le_rfl⟩

/-- The grouped scalar bank on the real large parent follows from the
proved ordinary banks. The frame and OLD cutoff are fixed; the extra future
indices are all attenuated to zero at t=0. -/
theorem old_hessian_parent_grouped_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    (∀ Q ∈ oldHessianMacroCells m,
      InverseBankConclusion M .globalInverse (bankObserverRootUnion Q 5)
        m (m+40) (bankPartialInsertionWeights m 1 0)) ∧
    eLpNorm (inverseBankGroupedRemainder .globalInverse (oldHessianMacroCells m)
      (fun Q => bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0)) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5/10^24:ℝ) ∧
    eLpNorm (inverseBankGroupedHistory (oldHessianMacroCells m)
      (fun Q => bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0)) 128
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (14103/10000:ℝ) := by
  have hgeo := old_hessian_macrocell_geometry m
  exact global_bank_of_states M h hM hg (oldHessianMacroCells m)
    (fun Q => bankObserverRootUnion Q 5) hgeo.1.le m (m+40) (by omega)
    (bankPartialInsertionWeights m 1 0)
    (fun k _ => bank_partial_insertion_weights_bounds m 1 0 (by norm_num) k)
    (fun Q hQ => (hgeo.2 Q hQ).2.1) (fun Q hQ => (hgeo.2 Q hQ).2.2)
    (fun k hk => hpast k (hk.trans hm))

/-- The actual grouped history is finite a.e. and has its positive rare
split on ENNReal itself. No bound through toReal can hide an infinite value. -/
theorem old_hessian_parent_grouped_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let B := inverseBankGroupedHistory (oldHessianMacroCells m)
        (fun Q => bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0) omega
      let R := inverseBankGroupedRemainder .globalInverse (oldHessianMacroCells m)
        (fun Q => bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0) omega
      B<⊤ ∧ R<⊤ ∧ B≤ENNReal.ofReal (14103/10000:ℝ)+R := by
  classical
  have hbank := (old_hessian_parent_grouped_bank M h hM hg N hpast m hm).1
  have hall : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ Q : ↥(oldHessianMacroCells m),
        bankFiniteRootHistoryMax (bankObserverRootUnion Q.val 5) M m (m+40)
          (bankPartialInsertionWeights m 1 0) omega<⊤ ∧
        bankFiniteRootHistoryMax (bankObserverRootUnion Q.val 5) M m (m+40)
          (bankPartialInsertionWeights m 1 0) omega ≤
          ENNReal.ofReal (inverseBankCap .globalInverse:ℝ)+
            ENNReal.ofReal (inverseBankPopulationRemainder .globalInverse
              (bankObserverRootUnion Q.val 5) M m (m+40) (bankPartialInsertionWeights m 1 0) omega) :=
    Filter.eventually_all.mpr (fun Q =>
      (hbank Q.val Q.property).history_finite.and (hbank Q.val Q.property).history_le)
  filter_upwards [hall] with omega homega
  dsimp only
  refine ⟨?_,?_,?_⟩
  · apply (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr
    intro Q hQ
    exact (homega ⟨Q,hQ⟩).1
  · apply (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr
    intro Q _
    exact ENNReal.ofReal_lt_top
  · apply Finset.sup_le
    intro Q hQ
    have hh := (homega ⟨Q,hQ⟩).2
    exact hh.trans (add_le_add (by norm_num [inverseBankCap])
      (Finset.le_sup (f := fun Q => ENNReal.ofReal (inverseBankPopulationRemainder .globalInverse
        (bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0) omega)) hQ))

end
end ASDExplicitGamma.Scalar
