module

public import ASDExplicitGamma.Native.ParentRowErrorPanelAssembly
public import ASDExplicitGamma.Native.ParentRowCompletedReturn

/-! The final generator and sixteen-row return after the finite error comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native Set
noncomputable section

/-- Close the generator once the finite error cap fits its exact panel block.
This explicit in-node input is discharged by the four-block assembly. -/
theorem parent_row_generator_panel_of_error
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (hstate : nativeInductionState M h n)
    (hpast : ∀ l < n, nativeInductionState M h l) (j : Fin 16)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (he : parentRowBandErrorCap M h n (j.val+1) r t≤theta M*parentRowPanelError j t) :
    (∫ ω,nativeSourceBandMeanGenerator M h n (j.val+1) t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      theta M*(parentRowB0 j+nativePanelValue (parentRowFields j) t)-
        parentBoundaryBandDirichletEnergy M h n (j.val+1)*
          (parentBoundaryBandInverseMean M n (j.val+1) t-2) := by
  have hh := parent_row_generator_affine_panel M h hM hg n hstate hpast j r hr U hU t ht
  have hh' := hh.trans (add_le_add le_rfl he)
  rw [←parent_row_panel_blocks_eq j t ht.1]
  exact hh'.trans_eq (by ring)

/-- Restore the completed true frame and all sixteen certified row caps
from the actual finite-shell error comparison at the earlier starting label.
The current induction state is derived from the strict-past hypothesis. -/
theorem parent_row_completed_bound_of_error_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (m : ℤ)
    (hpast : ∀ l < m, nativeInductionState M h l) (j : Fin 16)
    (he : ∀ t ∈ Ioo (0:ℝ) 1,
      parentRowBandErrorCap M h (m-((j.val+1:ℕ):ℤ)) (j.val+1) 5 t≤
        theta M*parentRowPanelError j t) :
    nativeCompletedSourceMean M m (j.val+1)≤
      ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ)) := by
  generalize hr : (5:ℕ)=r at he
  apply parent_row_completed_bound_of_generator M h hM hg m hpast j
  intro t ht
  let n := m-((j.val+1:ℕ):ℤ)
  have hn : n < m := by dsimp only [n]; omega
  obtain ⟨U,hU⟩ := descendantsAtDepth_nonempty (originCube 2 n) r
  exact parent_row_generator_panel_of_error M h hM hg n (hpast n hn)
    (fun l hl => hpast l (hl.trans hn)) j r hr.symm U hU t ⟨ht.1.le,ht.2.le⟩ (he t ht)

end
end ASDExplicitGamma.Native
