/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Gaussian.RealizationSeries
import ASDExplicitGamma.Model.Q3Moments

/-!
# Finite observations of the frozen q3 shell law
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.Gaussian

/-- The planar q3 covariance kernel at amplitude `h`. -/
noncomputable def q3CovarianceKernel (h : ℝ) (x y : Homogenization.Vec 2) : ℝ :=
  h ^ 2 * q3Cov ((x - y) 0) * q3Cov ((x - y) 1)

/-- The frozen q3 Gaussian hypothesis gives the same finite observation law for any finite index
type, after reindexing it by `Fin`. -/
theorem zeroShellLaw_map_finite_q3_observation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {K : Set (Homogenization.Vec 2)} {ι : Type} [Fintype ι]
    (x : ι → K) (t : ι → ℝ) :
    ((Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure).map
        (fun j => ∑ i, t i * j (x i : Homogenization.Vec 2) 1 0) =
      gaussianReal 0 (Real.toNNReal (
        ∑ i, ∑ i', t i * t i' * q3CovarianceKernel h
          (x i : Homogenization.Vec 2) (x i' : Homogenization.Vec 2))) := by
  classical
  let n := Fintype.card ι
  let e : ι ≃ Fin n := Fintype.equivFin ι
  let xFin : Fin n → Homogenization.Vec 2 := fun i => x (e.symm i)
  let tFin : Fin n → ℝ := fun i => t (e.symm i)
  have hobs (j : Algsuperdiff.Frozen.Assumptions.ShellField 2) :
      (∑ i, t i * j (x i : Homogenization.Vec 2) 1 0) =
        ∑ i : Fin n, tFin i * j (xFin i) 1 0 := by
    dsimp [tFin, xFin]
    simpa using (Equiv.sum_comp e.symm (fun i : ι => t i * j (x i) 1 0)).symm
  have hvariance :
      (∑ i : Fin n, ∑ i', tFin i * tFin i' *
        q3Cov ((xFin i - xFin i') 0) * q3Cov ((xFin i - xFin i') 1)) =
      ∑ i, ∑ i', t i * t i' *
        q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 0) *
        q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 1) := by
    dsimp [tFin, xFin]
    symm
    calc
      (∑ i : ι, ∑ i', t i * t i' *
          q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 0) *
          q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 1)) =
        ∑ i : Fin n, ∑ i', t (e.symm i) * t i' *
          q3Cov (((x (e.symm i) : Homogenization.Vec 2) -
            (x i' : Homogenization.Vec 2)) 0) *
          q3Cov (((x (e.symm i) : Homogenization.Vec 2) -
            (x i' : Homogenization.Vec 2)) 1) := by
            exact (Equiv.sum_comp e.symm (fun i : ι => ∑ i', t i * t i' *
              q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 0) *
              q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 1))).symm
      _ = ∑ i : Fin n, ∑ i' : Fin n, t (e.symm i) * t (e.symm i') *
          q3Cov (((x (e.symm i) : Homogenization.Vec 2) -
            (x (e.symm i') : Homogenization.Vec 2)) 0) *
          q3Cov (((x (e.symm i) : Homogenization.Vec 2) -
            (x (e.symm i') : Homogenization.Vec 2)) 1) := by
            congr 1
            funext i
            exact (Equiv.sum_comp e.symm (fun i' : ι => t (e.symm i) * t i' *
              q3Cov (((x (e.symm i) : Homogenization.Vec 2) -
                (x i' : Homogenization.Vec 2)) 0) *
              q3Cov (((x (e.symm i) : Homogenization.Vec 2) -
                (x i' : Homogenization.Vec 2)) 1))).symm
  have hvarianceKernel :
      h ^ 2 * (∑ i : Fin n, ∑ i', tFin i * tFin i' *
        q3Cov ((xFin i - xFin i') 0) * q3Cov ((xFin i - xFin i') 1)) =
      ∑ i, ∑ i', t i * t i' * q3CovarianceKernel h
        (x i : Homogenization.Vec 2) (x i' : Homogenization.Vec 2) := by
    calc
      _ = h ^ 2 * (∑ i, ∑ i', t i * t i' *
          q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 0) *
          q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 1)) := by
            rw [hvariance]
      _ = ∑ i, ∑ i', h ^ 2 * (t i * t i' *
          q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 0) *
          q3Cov (((x i : Homogenization.Vec 2) - (x i' : Homogenization.Vec 2)) 1)) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ i, ∑ i', t i * t i' * q3CovarianceKernel h
          (x i : Homogenization.Vec 2) (x i' : Homogenization.Vec 2) := by
            congr 1
            funext i
            congr 1
            funext i'
            simp [q3CovarianceKernel]
            ring
  calc
    _ = ((Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure).map
          (fun j => ∑ i : Fin n, tFin i * j (xFin i) 1 0) := by
            congr 1
            funext j
            exact hobs j
    _ = gaussianReal 0 (Real.toNNReal (h ^ 2 *
          ∑ i : Fin n, ∑ i', tFin i * tFin i' *
            q3Cov ((xFin i - xFin i') 0) * q3Cov ((xFin i - xFin i') 1))) := by
          exact hM.2 n xFin tFin
    _ = gaussianReal 0 (Real.toNNReal (
          ∑ i, ∑ i', t i * t i' * q3CovarianceKernel h
            (x i : Homogenization.Vec 2) (x i' : Homogenization.Vec 2))) := by
          rw [hvarianceKernel]

end ASDExplicitGamma.Gaussian
