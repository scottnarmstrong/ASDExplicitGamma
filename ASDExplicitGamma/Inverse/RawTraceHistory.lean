module

public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Inverse.RawWeakHistoryLp
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Cold.SquarePartitionProjection

/-! The literal depth-indexed four-load trace variables in the OLD true frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Cold
open MeasureTheory

/-- The actual four-load trace on a translated source cube. -/
noncomputable def rawCubeFourLoadTrace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  traceDefect (cubeSet Q)
    (Model.partialInsertedCoefficient M m t ω).toFun (Annealed.sigmaBar M m : ℝ)

/-- The source four-load trace at scale `q`, with the partially inserted coefficient. -/
noncomputable def rawDepthFourLoadTrace (M : ABKModel 2) (m q : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawCubeFourLoadTrace M m (originCube 2 q) t ω

/-- The depth-j source trace is the actual spatial average over the common
descendant tiling, as in the `Tbar_j` used in `Theta_o`. -/
noncomputable def rawWeakTraceSequence (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  squareCellMean Q j (fun C => rawCubeFourLoadTrace M m C.val t ω)

/-- The source weak history, interpreted as the normalized L²-convergent series
of its actual depth trace variables. -/
noncomputable def rawWeakTraceHistoryLp (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ)
    (hT : ∀ j, MemLp (rawWeakTraceSequence M m Q t · j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    Lp ℝ 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  rawWeakHistoryOfMemLp (Cutoff.cutoffSampleLaw M).toMeasure
    (fun j ω => rawWeakTraceSequence M m Q t ω j) hT

/-- The raw-trace transport envelope directly supplies the source bound
`‖Hbar‖₂ ≤ H_o` after summing its weighted depth profile. -/
theorem raw_weak_trace_history_lpNorm_le_of_envelope (M : ABKModel 2)
    (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (hT : ∀ j, MemLp (rawWeakTraceSequence M m Q t · j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (U : ℕ → ℝ)
    (hU : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * U j))
    (hbound : ∀ j, ‖(hT j).toLp (rawWeakTraceSequence M m Q t · j)‖ ≤ U j) :
    ‖rawWeakTraceHistoryLp M m Q t hT‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * U j := by
  exact raw_weak_history_of_memLp_lpNorm_le_of_envelope
    (Cutoff.cutoffSampleLaw M).toMeasure
    (fun j ω => rawWeakTraceSequence M m Q t ω j) hT U hU hbound

/-- The literal trace is the compact Gaussian model observable in the same true frame. -/
theorem raw_depth_four_load_trace_eq_model_observable (M : ABKModel 2) (m q : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    rawDepthFourLoadTrace M m q t ω =
      modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)
        (modelInsertedScalar (closure (cubeSet (originCube 2 q))) m t ω) := by
  exact (inserted_response_true_frame M m q t ω).symm

/-- The depth trace variables are nonnegative in the common OLD true frame. -/
theorem raw_depth_four_load_trace_nonneg (M : ABKModel 2) (m q : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ rawDepthFourLoadTrace M m q t ω := by
  rw [raw_depth_four_load_trace_eq_model_observable]
  exact modelTraceObservable_nonneg q M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 _

/-- Every actual depth variable in the OLD true frame is nonnegative. -/
theorem raw_cube_four_load_trace_nonneg (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ rawCubeFourLoadTrace M m Q t ω := by
  obtain ⟨ell, hEll⟩ := exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hU : cubeSet Q ⊆ openCubeSet (originCube 2 ell) := by
    exact subset_closure.trans hEll
  have hcoeff := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
    (measurableSet_cubeSet Q) hU
  exact Variational.traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hcoeff
    (Annealed.sigmaBar_characterization M m).1

/-- Every actual depth-average variable in the OLD true frame is nonnegative. -/
theorem raw_weak_trace_sequence_nonneg (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    0 ≤ rawWeakTraceSequence M m Q t ω j := by
  unfold rawWeakTraceSequence squareCellMean
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro C hC
    exact raw_cube_four_load_trace_nonneg M m C.val t ht ω

end ASDExplicitGamma.Inverse
