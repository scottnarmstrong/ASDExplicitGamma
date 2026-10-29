module

public import ASDExplicitGamma.Cold.NativeHistoryMaximum

/-! # The genuine native complete history supplies the actual P1--P6 depth bounds -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- The actual finite-union maximum has exactly the source population cost at every depth. -/
theorem coldNativeHistory_maximum_norm {M : ABKModel 2} {m : ℤ} {R S : ℝ}
    (hroot : root20 M m ≤ ENNReal.ofReal R) (hstrong : strong20 M m ≤ ENNReal.ofReal S)
    (j r : ℕ) :
    lpNorm (coldFiniteMaximum (coldNativeHistoryArray M m j r)) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      (9:ℝ)^((r:ℝ)/20)*lpNorm (cutoffTraceDefect M m (m+(j:ℤ)-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  have h := coldFiniteMaximum_lpNorm_le (coldNativeHistoryArray_memLp hroot hstrong j r)
    (fun i => coldNativeCellTrace_measurable M m (coldNativeHistoryCell m j r i)) lpNorm_nonneg
    (fun i => (congrArg ENNReal.toReal ((coldNativeHistoryArray_sameLaw M m j r i).eLpNorm_eq (p := 20))).le)
  rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,cold_history_population_factor] at h
  exact h

/-- Almost surely, every actual source-cell trace is bounded by 3^(r/4) times the
complete native history; the root trace has factor one. -/
theorem cold_native_history_depth_bounds {M : ABKModel 2} {m : ℤ} {R S : ℝ}
    (hroot : root20 M m ≤ ENNReal.ofReal R) (hS : 0 ≤ S)
    (hstrong : strong20 M m ≤ ENNReal.ofReal S) (j : ℕ) :
    let F := coldNativePlateauFamily M m (originCube 2 (m+(j:ℤ)))
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, (F.atDepth 0).parentTrace ω ≤ coldNativeHistory M m j ω) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ r, ∀ C : SquareCells (originCube 2 (m+(j:ℤ))) r,
      (F.atDepth r).cellTrace C ω ≤ (3:ℝ)^((r:ℝ)/4)*coldNativeHistory M m j ω) := by
  dsimp only
  let Z := fun r => coldFiniteMaximum (coldNativeHistoryArray M m j r)
  let b := fun r : ℕ => coldHistoryBeta^r*
    lpNorm (cutoffTraceDefect M m (m+(j:ℤ)-(r:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure
  have hZ (r : ℕ) : MemLp (Z r) 20 (Cutoff.cutoffSampleLaw M).toMeasure :=
    memLp_coldFiniteMaximum (coldNativeHistoryArray_memLp hroot hstrong j r)
      (fun i => coldNativeCellTrace_measurable M m (coldNativeHistoryCell m j r i))
  have hcap (r : ℕ) : lpNorm (fun ω => coldHistoryAlpha^r*Z r ω) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ b r := by
    rw [cold_lpNorm_nonneg_mul _ (pow_nonneg coldHistoryAlpha_pos.le _)]
    have hh := mul_le_mul_of_nonneg_left (coldNativeHistory_maximum_norm hroot hstrong j r)
      (pow_nonneg coldHistoryAlpha_pos.le r)
    rw [← mul_assoc,cold_history_population_weight] at hh
    exact hh
  have hb : Summable b := coldNativeHistory_normSeries_summable hS hstrong j
  have hdepth := cold_history_depth_bound_ae hZ hb hcap
    (Filter.Eventually.of_forall (fun ω r => coldNativeHistory_maximum_nonneg M m j r ω))
    (Filter.Eventually.of_forall (coldNativeHistory_maximum_mono M m j))
  let Q := originCube 2 (m+(j:ℤ))
  let F := coldNativePlateauFamily M m Q
  have hmax : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ r, F.traceMaximum r ω ≤
      (3:ℝ)^((r:ℝ)/4)*coldNativeHistory M m j ω := by
    filter_upwards [hdepth] with ω hω r
    rw [← coldNativeHistory_maximum_eq]
    exact hω r
  constructor
  · filter_upwards [hmax] with ω hω
    have h0 := hω 0
    norm_num only [Nat.cast_zero,zero_div,Real.rpow_zero,one_mul] at h0
    have hparent : (F.atDepth 0).parentTrace ω ≤ F.traceMaximum 0 ω := by
      exact le_coldFiniteMaximum (fun C : SquareCells Q 0 => (F.atDepth 0).cellTrace C) ω
        ⟨Q,by simp only [descendantsAtDepth_zero,Finset.mem_singleton]⟩
    exact hparent.trans h0
  · filter_upwards [hmax] with ω hω r C
    exact (le_coldFiniteMaximum (fun C : SquareCells Q r => (F.atDepth r).cellTrace C) ω C).trans (hω r)

end ASDExplicitGamma.Cold
