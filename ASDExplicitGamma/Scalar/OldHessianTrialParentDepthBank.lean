module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalDepthBank
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedLocalReal

/-! The original parent fine-depth block maxima lie in the same grouped population. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- A finite grouped maximum covers the original population whenever
its actual members are covered; no cardinal or ambient enumeration is used. -/
theorem old_hessian_finite_grouped_max_le {I D : Type*} [DecidableEq I]
    (s : Finset I) (t : Finset D) (P : D → Finset I) (f : I → ℝ≥0∞)
    (hcover : ∀ V∈s,∃ W∈t,V∈P W) :
    (Finset.univ : Finset ↥s).sup (fun V => f V.val)≤
      t.sup (fun W => (Finset.univ : Finset ↥(P W)).sup (fun V => f V.val)) := by
  classical
  apply Finset.sup_le
  intro V _
  obtain ⟨W,hW,hV⟩ := hcover V.val V.property
  exact (Finset.le_sup (f := fun U : ↥(P W) => f U.val) (Finset.mem_univ ⟨V.val,hV⟩)).trans
    (Finset.le_sup (f := fun W => (Finset.univ : Finset ↥(P W)).sup (fun U => f U.val)) hW)

/-- Every depth134+j parent block belongs to a genuine macrocell's r5
population. This estimate is extended-valued, before any real conversion. -/
theorem old_hessian_parent_depth_ofReal_le_grouped (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    ENNReal.ofReal (lemmaVInverseDepthMax (originCube 2 (m+129))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)) (134+j))≤oldHessianGroupedDepthBlocks M m j ω := by
  classical
  let s := descendantsAtDepth (originCube 2 (m+129)) (134+j)
  let I := oldHessianMacroCells m
  let P := fun D => bankObserverDepthRootUnion D 5 j
  let f := fun V => ENNReal.ofReal (rootInverseResponse M V m (m+40) (bankPartialInsertionWeights m 1 0) ω)
  have hcover (V : TriadicCube 2) (hV : V∈s) : ∃ D∈I,V∈P D := by
    have hdepth : V∈descendantsAtDepth (originCube 2 (m+129)) (89+(45+j)) := by
      simpa only [show 89+(45+j)=134+j by omega] using hV
    obtain ⟨D,hD,hVD⟩ := exists_descendant_ancestor_at_depth 89 (45+j) hdepth
    refine ⟨D,hD,?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨5,Finset.mem_range.mpr (by omega),?_⟩
    change V∈descendantsAtDepth D (40+5+j)
    simpa only [show 40+5+j=45+j by omega] using hVD
  have hh := old_hessian_finite_grouped_max_le s I P f hcover
  rw [←old_hessian_physical_depth_max M (m+129) m ω (originCube 2 (m+129)) (Set.Subset.refl _) (134+j)]
  exact hh

/-- On one common event, all actual parent depths use the same local
baseline and correlated grouped rare variables as the source weak proxy. -/
theorem old_hessian_actual_parent_depth_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ j : ℕ,
      lemmaVInverseDepthMax (originCube 2 (m+129))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient (m+129) m ω)) (134+j)≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω := by
  have hall := ae_all_iff.mpr (fun j => (old_hessian_grouped_local_depth_bank M h hM hg N hpast m hm j).2.2)
  filter_upwards [hall] with ω hω
  intro j
  have hR : oldHessianGroupedDepthRare M m j ω<⊤ :=
    (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr (fun _ _ => ENNReal.ofReal_lt_top)
  have hb : 0≤(inverseBankCap .localInverse:ℝ)*bankDepthFrame M j :=
    mul_nonneg (by norm_num [inverseBankCap]) (bankDepthFrame_pos M j).le
  have hh := (old_hessian_parent_depth_ofReal_le_grouped M m ω j).trans (hω j).2
  have hfinite : ENNReal.ofReal ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j)+
      oldHessianGroupedDepthRare M m j ω≠⊤ :=
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hR⟩).ne
  have ht := ENNReal.toReal_mono hfinite hh
  rw [ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg _ _ _),
    ENNReal.toReal_add ENNReal.ofReal_ne_top hR.ne,ENNReal.toReal_ofReal hb] at ht
  exact ht

end
end ASDExplicitGamma.Scalar
