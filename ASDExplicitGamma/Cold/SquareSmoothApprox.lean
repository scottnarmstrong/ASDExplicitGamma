module

public import ASDExplicitGamma.Cold.SquareTransportForm

/-! # Canonical smooth H¹ approximation on the square, with explicit representative bridges -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- A fixed positive interior approximation radius. -/
theorem cubeHalfRadius_pos (Q : TriadicCube 2) : 0 < cubeRadius Q / 2 := by
  exact div_pos (cubeRadius_pos Q) (by norm_num)

/-- The approximation ball is strictly inside the open square. -/
theorem cubeHalfRadius_closedBall_subset (Q : TriadicCube 2) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q / 2) ⊆ openCubeSet Q := by
  rw [← ball_cubeCenter_eq_openCubeSet]
  apply Metric.closedBall_subset_ball
  linarith only [cubeRadius_pos Q]

/-- Actual globally smooth approximants supplied by the proved convex-domain density theorem. -/
def cubeSmoothApprox (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) (n : ℕ) :
    H1Function (openCubeSet Q) :=
  H1Function.convexApproxSmoothH1 (isOpenBoundedConvexDomain_openCubeSet Q) u
    (cubeCenter Q) (cubeHalfRadius_pos Q) n

/-- The exact smooth representative, rather than just an L² equality. -/
theorem cubeSmoothApprox_toFun (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) (n : ℕ) :
    (cubeSmoothApprox Q u n).toFun =
      convexApproxSmoothRepresentative (openCubeSet Q) (unitConvexApproxKernel (d := 2))
        u.toFun (cubeCenter Q) (cubeRadius Q / 2) (unitConvexApproxScale n) :=
  H1Function.convexApproxSmoothH1_toFun (isOpenBoundedConvexDomain_openCubeSet Q) u
    (cubeCenter Q) (cubeHalfRadius_pos Q) n

/-- Each approximation is globally C∞. -/
theorem contDiff_cubeSmoothApprox (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (cubeSmoothApprox Q u n).toFun := by
  rw [cubeSmoothApprox_toFun]
  exact contDiff_convexApproxSmoothRepresentative (measurableSet_openCubeSet Q)
    (isConvexApproxKernel_unitConvexApproxKernel (d := 2)) (by norm_num) u.memL2
    (cubeHalfRadius_pos Q) (H1Function.unitConvexApproxScale_pos_meanZero n)

/-- The chosen weak gradient of the approximants is their classical derivative. -/
theorem cubeSmoothApprox_grad (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) (n : ℕ)
    (x : Vec 2) (i : Fin 2) :
    (cubeSmoothApprox Q u n).grad x i = smoothPartial (cubeSmoothApprox Q u n).toFun i x := by
  unfold cubeSmoothApprox
  rw [H1Function.convexApproxSmoothH1_grad]
  unfold smoothPartial
  rw [H1Function.convexApproxSmoothH1_toFun]

/-- Strong L² convergence of the actual function values. -/
theorem tendsto_cubeSmoothApprox_value (Q : TriadicCube 2) (u : H1Function (openCubeSet Q)) :
    Tendsto (fun n => (cubeSmoothApprox Q u n).toScalarL2) atTop (𝓝 u.toScalarL2) :=
  H1Function.tendsto_convexApproxSmoothH1_toScalarL2 (isOpenBoundedConvexDomain_openCubeSet Q) u
    (cubeHalfRadius_closedBall_subset Q) (cubeHalfRadius_pos Q)

/-- Strong L² convergence of every actual weak gradient coordinate. -/
theorem tendsto_cubeSmoothApprox_gradient (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (i : Fin 2) :
    Tendsto (fun n => (cubeSmoothApprox Q u n).gradCoordToScalarL2 i) atTop
      (𝓝 (u.gradCoordToScalarL2 i)) :=
  H1Function.tendsto_convexApproxSmoothH1_gradCoordToScalarL2
    (isOpenBoundedConvexDomain_openCubeSet Q) u
    (cubeHalfRadius_closedBall_subset Q) (cubeHalfRadius_pos Q) i

/-- The source cutoff integration-by-parts identity for arbitrary H¹ fields. -/
theorem squareTransportForm_eq_boundary (Q : TriadicCube 2) {φ : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφs : tsupport φ ⊆ closedSquare Q)
    (M : ℝ) (hM : ∀ x, ‖φ x‖ ≤ M) (u w : H1Function (openCubeSet Q)) :
    squareTransportForm Q φ u w = squareTransportBoundaryForm Q φ u w := by
  have hφtop : MemLp φ ⊤ (volume.restrict (openCubeSet Q)) :=
    memLp_top_of_bound hφ.continuous.aestronglyMeasurable M (Filter.Eventually.of_forall hM)
  have hT := tendsto_squareTransportForm Q hφtop M (Filter.Eventually.of_forall hM)
    (tendsto_cubeSmoothApprox_gradient Q u) (tendsto_cubeSmoothApprox_gradient Q w)
  have hB := tendsto_squareTransportBoundaryForm Q hφ (tendsto_cubeSmoothApprox_value Q u)
    (tendsto_cubeSmoothApprox_gradient Q w)
  have heq (n : ℕ) : squareTransportForm Q φ (cubeSmoothApprox Q u n) (cubeSmoothApprox Q w n) =
      squareTransportBoundaryForm Q φ (cubeSmoothApprox Q u n) (cubeSmoothApprox Q w n) :=
    squareTransportForm_eq_boundary_of_smooth Q hφ hφs hφtop _ _
      (contDiff_cubeSmoothApprox Q u n) (contDiff_cubeSmoothApprox Q w n)
      (cubeSmoothApprox_grad Q u n) (cubeSmoothApprox_grad Q w n)
  exact tendsto_nhds_unique hT (hB.congr' (Filter.Eventually.of_forall (fun n => (heq n).symm)))

end ASDExplicitGamma.Cold
