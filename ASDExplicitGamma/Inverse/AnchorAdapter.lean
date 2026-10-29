module

public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Model.Translation

/-! Identification of inverse-root responses with the literal cutoff coefficient
and its true completed-label frame. Partial insertions keep that same frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

/-- The compact four-load response agrees with the actual partial insertion
in the OLD true frame for every deterministic insertion parameter. -/
theorem inserted_response_true_frame (M : ABKModel 2) (m k : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable k M.nu (Annealed.sigmaBar M m : ℝ)
      (modelInsertedScalar (closure (cubeSet (originCube 2 k))) m t ω) =
      traceDefect (cubeSet (originCube 2 k))
        (Model.partialInsertedCoefficient M m t ω).toFun (Annealed.sigmaBar M m : ℝ) := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact
    (closure (cubeSet (originCube 2 k))) (isBounded_cubeSet (originCube 2 k)).isCompact_closure
  exact modelTraceObservable_inserted_eq_traceDefect k M ell m hK _ t ω

/-- At zero insertion, the same response is precisely the frozen cutoff observable. -/
theorem cutoff_response_true_frame (M : ABKModel 2) (m k : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable k M.nu (Annealed.sigmaBar M m : ℝ)
      (modelInsertedScalar (closure (cubeSet (originCube 2 k))) m 0 ω) =
      cutoffTraceDefect M m k ω := by
  have he : Model.partialInsertedCoefficient M m 0 ω = Cutoff.coefficientCutoff M.nu m ω := by
    ext x i j
    change Cutoff.coefficientCutoff M.nu m ω x i j +
      Real.sqrt 0 * (ω.1 (m + 1)).forgetShell x i j = _
    rw [Real.sqrt_zero, zero_mul, add_zero]
  rw [inserted_response_true_frame, he]
  rfl

end ASDExplicitGamma.Inverse
