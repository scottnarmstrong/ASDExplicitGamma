module

public import ASDExplicitGamma.Cold.NativeHistoryTable
public import ASDExplicitGamma.Cold.TraceHistoryMonotone
public import ASDExplicitGamma.Cold.HistoryDepthBound

/-! # The actual native complete history controls every own-cell depth -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- Exact finite maxima are unchanged by a finite bijective reindexing. -/
theorem coldFiniteMaximum_reindex {Ω ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (e : ι ≃ κ) (X : κ → Ω → ℝ) (ω : Ω) :
    coldFiniteMaximum (fun i => X (e i)) ω = coldFiniteMaximum X ω := by
  apply le_antisymm
  · obtain ⟨i,hi⟩ := coldFiniteMaximum_eq_some (fun i => X (e i)) ω
    rw [hi]
    exact le_coldFiniteMaximum X ω (e i)
  · obtain ⟨k,hk⟩ := coldFiniteMaximum_eq_some X ω
    rw [hk]
    simpa only [Equiv.apply_symm_apply] using le_coldFiniteMaximum (fun i => X (e i)) ω (e.symm k)

/-- The finite indexed native maximum is the actual optimizer family's cell maximum. -/
theorem coldNativeHistory_maximum_eq (M : ABKModel 2) (m : ℤ) (j r : ℕ) (ω : Cutoff.CutoffSample 2) :
    coldFiniteMaximum (coldNativeHistoryArray M m j r) ω =
      (coldNativePlateauFamily M m (originCube 2 (m+(j:ℤ)))).traceMaximum r ω := by
  let Q := originCube 2 (m+(j:ℤ))
  have he : (fun C : SquareCells Q r => ((coldNativePlateauFamily M m Q).atDepth r).cellTrace C) =
      (fun C => coldNativeCellTrace M m C.val) := by
    funext C ω
    exact coldNativePlateauFamily_cellTrace M m Q r C ω
  unfold ColdPlateauFamily.traceMaximum
  rw [he]
  exact coldFiniteMaximum_reindex (coldCellEquiv Q r) (fun C => coldNativeCellTrace M m C.val) ω

/-- The actual depthwise native trace maxima are nonnegative. -/
theorem coldNativeHistory_maximum_nonneg (M : ABKModel 2) (m : ℤ) (j r : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ coldFiniteMaximum (coldNativeHistoryArray M m j r) ω := by
  rw [coldNativeHistory_maximum_eq]
  exact ColdPlateauFamily.traceMaximum_nonneg _ _ _

/-- The actual native maxima increase with depth by genuine trace subadditivity. -/
theorem coldNativeHistory_maximum_mono (M : ABKModel 2) (m : ℤ) (j : ℕ) (ω : Cutoff.CutoffSample 2) :
    Monotone (fun r => coldFiniteMaximum (coldNativeHistoryArray M m j r) ω) := by
  intro r s hrs
  change coldFiniteMaximum (coldNativeHistoryArray M m j r) ω ≤ coldFiniteMaximum (coldNativeHistoryArray M m j s) ω
  rw [coldNativeHistory_maximum_eq,coldNativeHistory_maximum_eq]
  exact ColdPlateauFamily.traceMaximum_mono _ ω hrs

/-- The exact strong input supplies summability of the complete unnormalized weighted norm series. -/
theorem coldNativeHistory_normSeries_summable {M : ABKModel 2} {m : ℤ} {S : ℝ}
    (hS : 0 ≤ S) (hstrong : strong20 M m ≤ ENNReal.ofReal S) (j : ℕ) :
    Summable (fun r : ℕ => coldHistoryBeta^r*
      lpNorm (cutoffTraceDefect M m (m+(j:ℤ)-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure) := by
  apply (summable_nat_add_iff j).mp
  have hs := (cold_native_strong_sum hS hstrong).1.mul_left
    (coldHistoryBeta^j/(1-coldHistoryAlpha))
  have he (k : ℕ) : coldHistoryBeta^(k+j)*
      lpNorm (cutoffTraceDefect M m (m+(j:ℤ)-((k+j:ℕ):ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure =
      (coldHistoryBeta^j/(1-coldHistoryAlpha))*coldNativeStrongRealTerm M m k := by
    have hscale : m+(j:ℤ)-((k+j:ℕ):ℤ) = m-(k:ℤ) := by omega
    rw [hscale,pow_add]
    unfold coldNativeStrongRealTerm
    field_simp [ne_of_gt (sub_pos.mpr coldHistoryAlpha_lt_one)]
  simp_rw [he]
  exact hs

end ASDExplicitGamma.Cold
