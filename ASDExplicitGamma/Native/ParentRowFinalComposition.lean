module

public import ASDExplicitGamma.Native.ParentRowGeneratorPanel
public import ASDExplicitGamma.Native.ParentWeakFieldComparison
public import ASDExplicitGamma.Native.ParentBoundarySums
public import ASDExplicitGamma.Native.ParentBoundaryFlatCap

/-! The boundary-fixed OLD parent return, consuming the proved weak-field,
flat-cap and paired-charge payments and the exact sixteen-row certificates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native Set
noncomputable section

/-- All sixteen completed rows follow from precisely the flat and paired-charge
supplier statements. The weak-field comparison, current starting state,
heat return, signed inverse payment, and rational certification are discharged
inside the proof. The two block premises are explicit in-node dependencies. -/
theorem parent_row_completed_bound_of_flat_charge
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (m : ℤ)
    (hpast : ∀ l < m, nativeInductionState M h l) (j : Fin 16)
    (hflat : ∀ t ∈ Ioo (0:ℝ) 1,
      let f := fun k => (parentRowFields j).getD k 0
      let X := parentRowPanelWeak j t
      let H := parentRowPanelHistory j t
      let A := 1+2*H+Real.sqrt (2*H)
      (∑ i : Fin (j.val+1),parentRowFlatCap M (m-((j.val+1:ℕ):ℤ)) (j.val+1) 5 t
        (q3ModelAmplitude M h ((m-((j.val+1:ℕ):ℤ))+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M (m-((j.val+1:ℕ):ℤ)):ℝ))
        (q3ModelLength ((m-((j.val+1:ℕ):ℤ))+((i.val+1:ℕ):ℤ))))≤
        theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4+
          2*Real.sqrt 2*Real.sqrt ((1+inverseHistoryDiscount)*A*H)*f 9*f 5+
          (3683/2500:ℝ)*(f 4)^2+A*(f 5)^2))
    (hcharge : ∀ t ∈ Ioo (0:ℝ) 1,
      let f := fun k => (parentRowFields j).getD k 0
      let X := parentRowPanelWeak j t
      (∑ i : Fin (j.val+1),parentRowChargeCap M (m-((j.val+1:ℕ):ℤ)) (j.val+1) 5 t
        (q3ModelAmplitude M h ((m-((j.val+1:ℕ):ℤ))+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M (m-((j.val+1:ℕ):ℤ)):ℝ))
        (q3ModelLength ((m-((j.val+1:ℕ):ℤ))+((i.val+1:ℕ):ℤ))))≤
        theta M*(2*f 6*Real.sqrt X+2*f 7*Real.sqrt (2*X))) :
    nativeCompletedSourceMean M m (j.val+1)≤
      ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ)) := by
  apply parent_row_completed_bound_of_error_caps M h hM hg m hpast j
  intro t ht
  let n := m-((j.val+1:ℕ):ℤ)
  have hn : n < m := by dsimp only [n]; omega
  exact parent_row_band_error_panel_of_flat_charge M h hg n (hpast n hn) j t
    ⟨ht.1.le,ht.2.le⟩ (parent_weak_panel_comparison j t ⟨ht.1.le,ht.2.le⟩)
    (hflat t ht) (hcharge t ht)

/-- Consume the paired-charge theorem on the actual starting band.
Only the finite-shell flat-cap comparison remains an in-node premise. -/
theorem parent_row_completed_bound_of_flat
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (m : ℤ)
    (hpast : ∀ l < m, nativeInductionState M h l) (j : Fin 16)
    (hflat : ∀ t ∈ Ioo (0:ℝ) 1,
      let f := fun k => (parentRowFields j).getD k 0
      let X := parentRowPanelWeak j t
      let H := parentRowPanelHistory j t
      let A := 1+2*H+Real.sqrt (2*H)
      (∑ i : Fin (j.val+1),parentRowFlatCap M (m-((j.val+1:ℕ):ℤ)) (j.val+1) 5 t
        (q3ModelAmplitude M h ((m-((j.val+1:ℕ):ℤ))+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M (m-((j.val+1:ℕ):ℤ)):ℝ))
        (q3ModelLength ((m-((j.val+1:ℕ):ℤ))+((i.val+1:ℕ):ℤ))))≤
        theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4+
          2*Real.sqrt 2*Real.sqrt ((1+inverseHistoryDiscount)*A*H)*f 9*f 5+
          (3683/2500:ℝ)*(f 4)^2+A*(f 5)^2))
 :
    nativeCompletedSourceMean M m (j.val+1)≤
      ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ)) := by
  apply parent_row_completed_bound_of_flat_charge M h hM hg m hpast j hflat
  intro t ht
  let n := m-((j.val+1:ℕ):ℤ)
  have hn : n < m := by dsimp only [n]; omega
  have hh := parent_boundary_paired_charge_panel M h hg n (hpast n hn) j t
    ⟨ht.1.le,ht.2.le⟩ (parent_weak_panel_comparison j t ⟨ht.1.le,ht.2.le⟩)
  simpa only [parentRowChargeCap,parentRowWeakAllowance,parentRowPanelWeak] using hh

/-- Each of the sixteen actual completed parent rows obeys its certified
exact rational cap. The proof retains the paired centered boundary charges,
the signed inverse contribution, and the true scalar frame. No row, moment,
generator, or panel estimate is assumed. -/
theorem native_completed_parent_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (m : ℤ)
    (hpast : ∀ l < m, nativeInductionState M h l) (j : Fin 16) :
    nativeCompletedSourceMean M m (j.val+1)≤
      ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD (j.val+1) 0:ℚ):ℝ)) := by
  apply parent_row_completed_bound_of_flat M h hM hg m hpast j
  intro t ht
  let n := m-((j.val+1:ℕ):ℤ)
  have hn : n < m := by dsimp only [n]; omega
  exact parent_row_band_flat_cap M h hg n (hpast n hn) j t
    ⟨ht.1.le,ht.2.le⟩ (parent_weak_panel_comparison j t ⟨ht.1.le,ht.2.le⟩)

/-- The same certified cap for an arbitrary parent depth from one to sixteen. -/
theorem native_completed_parent_bounds
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (m : ℤ)
    (hpast : ∀ l < m, nativeInductionState M h l)
    (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) :
    nativeCompletedSourceMean M m height≤
      ENNReal.ofReal (theta M*((nativeBoundaryParentCaps.getD height 0:ℚ):ℝ)) := by
  let j : Fin 16 := ⟨height-1,by omega⟩
  have hj : j.val+1=height := by dsimp only [j]; omega
  simpa only [hj] using native_completed_parent_bound M h hM hg m hpast j

end
end ASDExplicitGamma.Native
