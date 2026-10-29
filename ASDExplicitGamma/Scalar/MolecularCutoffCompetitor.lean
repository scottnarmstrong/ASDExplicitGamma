module

public import ASDExplicitGamma.Scalar.MolecularCompetitor
public import ASDExplicitGamma.Scalar.MolecularUpperBound
public import ASDExplicitGamma.Model.Cutoff

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Response
open ASDExplicitGamma.Variational

/-- The actual planar cutoff coefficient has its literal stream amplitude. -/
theorem coefficientCutoff_eq_planar (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Cutoff.coefficientCutoff M.nu m ω x =
      responsePlanarCoefficient M.nu (Cutoff.cutoffValue m ω x 1 0) := by
  have hs := Cutoff.cutoff_skew m ω x
  have h00 := congrArg (fun A : Mat 2 => A 0 0) hs
  have h11 := congrArg (fun A : Mat 2 => A 1 1) hs
  have h01 := congrArg (fun A : Mat 2 => A 1 0) hs
  change Cutoff.cutoffValue m ω x 0 0 = -Cutoff.cutoffValue m ω x 0 0 at h00
  change Cutoff.cutoffValue m ω x 1 1 = -Cutoff.cutoffValue m ω x 1 1 at h11
  change Cutoff.cutoffValue m ω x 0 1 = -Cutoff.cutoffValue m ω x 1 0 at h01
  rw [ASDExplicitGamma.Model.coefficientCutoff_eq_nu_add_cutoffValue]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ, h01] <;> linarith only [h00, h11]

/-- The physical spatial average of the actual completed stream square. -/
noncomputable def cutoffStreamSquareAverage (m k : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  volumeAverage (cubeSet (originCube 2 k)) (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 2)

/-- Actual stream-square integrability follows from regularity on the compact cube closure. -/
theorem cutoff_stream_square_integrable (m k : ℤ) (ω : Cutoff.CutoffSample 2) :
    IntegrableOn (fun x => Cutoff.cutoffValue m ω x 1 0 ^ 2) (cubeSet (originCube 2 k)) := by
  let Q := originCube 2 k
  apply ((Cutoff.continuous_cutoffValue_entry m ω 1 0).pow 2).continuousOn.integrableOn_of_subset_isCompact
    (isBounded_cubeSet Q).isCompact_closure (measurableSet_cubeSet Q) subset_closure
  exact (volume_cubeSet_lt_top Q).ne

/-- Pointwise molecular competitor bound on every observation scale, at the
true frame of the completed label. -/
theorem cutoffTraceDefect_le_molecular_competitor (M : ABKModel 2) (m k : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    cutoffTraceDefect M m k ω ≤
      2 * ((Annealed.sigmaBar M m : ℝ) - M.nu) ^ 2 /
        (M.nu * (Annealed.sigmaBar M m : ℝ)) +
      2 * cutoffStreamSquareAverage m k ω / (M.nu * (Annealed.sigmaBar M m : ℝ)) := by
  obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M m ω (originCube 2 k)
  have he : (Cutoff.coefficientCutoff M.nu m ω).toFun =
      (fun x => responsePlanarCoefficient M.nu (Cutoff.cutoffValue m ω x 1 0)) :=
    funext (coefficientCutoff_eq_planar M m ω)
  rw [he] at hEll
  have hs : 0 < (Annealed.sigmaBar M m : ℝ) := M.nu_pos.trans_le (nu_le_sigmaBar M m)
  have hc := molecular_traceDefect_competitor M.nu_pos hs
    (fun x => Cutoff.cutoffValue m ω x 1 0) hEll (cutoff_stream_square_integrable m k ω)
  change traceDefect (cubeSet (originCube 2 k)) (Cutoff.coefficientCutoff M.nu m ω).toFun _ ≤ _
  rw [he]
  exact hc

end ASDExplicitGamma.Scalar
