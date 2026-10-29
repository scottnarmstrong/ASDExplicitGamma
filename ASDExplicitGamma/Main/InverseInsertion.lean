module

public import ASDExplicitGamma.Main.InverseObservable

/-! Exact inverse-observable identification before heat differentiation. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Response Algsuperdiff.Section3

/-- Extracting the lower-right trace from two exact frame trace identities
is pure scalar algebra; no matrix term is elaborated by arithmetic tactics. -/
theorem main_inverse_trace_algebra (a b c d : ℝ)
    (h1 : a + b - 4 = c + d - 4)
    (h2 : (1 / 2 : ℝ) * a + 2 * b - 4 = (1 / 2 : ℝ) * c + 2 * d - 4) : b = d := by
  linarith only [h1, h2]

/-- The compact inverse test is exactly the actual inverse trace, using the
already proved trace identification at two deterministic frame parameters. -/
theorem mainInverseObservable_inserted (M : ABKModel 2) (m n : ℤ) (t : ℝ)
    (omega : Cutoff.CutoffSample 2) :
    mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ)
      (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 n))) m t omega) =
        mainInsertionInverseTrace M m n t omega := by
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  let A := coarseBlockMatrix (cubeSet (originCube 2 n))
    (responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ
        (Gaussian.modelInsertedScalar (closure (cubeSet (originCube 2 n))) m t omega)))
  let B := coarseBlockMatrix (cubeSet (originCube 2 n)) (Model.partialInsertedCoefficient M m t omega).toFun
  have h1 : Matrix.trace A.upperLeft + Matrix.trace A.lowerRight - 4 =
      Matrix.trace B.upperLeft + Matrix.trace B.lowerRight - 4 := by
    have h := Gaussian.modelTraceObservable_inserted_eq_traceDefect n M ell m hK 1 t omega
    simpa only [Gaussian.modelTraceObservable, traceDefect, inv_one, one_mul] using h
  have h2 : (1 / 2 : ℝ) * Matrix.trace A.upperLeft + 2 * Matrix.trace A.lowerRight - 4 =
      (1 / 2 : ℝ) * Matrix.trace B.upperLeft + 2 * Matrix.trace B.lowerRight - 4 := by
    have h := Gaussian.modelTraceObservable_inserted_eq_traceDefect n M ell m hK 2 t omega
    simpa only [Gaussian.modelTraceObservable, traceDefect, one_div] using h
  exact congrArg (fun r : ℝ => (Annealed.sigmaBar M m : ℝ) * r)
    (main_inverse_trace_algebra _ _ _ _ h1 h2)

end ASDExplicitGamma.Main
