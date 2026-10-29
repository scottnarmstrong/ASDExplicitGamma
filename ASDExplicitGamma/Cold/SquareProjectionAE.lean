module

public import ASDExplicitGamma.Cold.PlateauGradientWeights

/-! # Cell projections respect the actual almost-everywhere stream identity -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Actual cell projection is independent of the chosen L² representative. -/
theorem square_scalar_projection_congr_ae (Q : TriadicCube 2) (r : ℕ) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[volume.restrict (openCubeSet Q)] g) : cubeProjection Q r f = cubeProjection Q r g := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet r hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth g hR hxR]
    unfold cubeAverage
    congr 1
    exact integral_congr_ae (ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hfg)
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q _ _ hx]

/-- The constant quarter-turn commutes with the actual coordinate projections. -/
theorem squareProjection_quarterTurn (Q : TriadicCube 2) (r : ℕ) (G : Vec 2 → Vec 2) :
    squareProjection Q r (fun x => squareQuarterTurn (G x)) =
      fun x => squareQuarterTurn (squareProjection Q r G x) := by
  funext x i
  fin_cases i
  · change cubeProjection Q r (fun y => -G y 1) x = -cubeProjection Q r (fun y => G y 1) x
    have heq : (fun y => -G y 1) = (fun y => (-1 : ℝ) * G y 1) := by funext y; ring
    rw [heq, projection_smul]
    ring
  · rfl

/-- The quarter-turn preserves the actual normalized vector energy. -/
theorem squareVectorEnergy_quarterTurn (Q : TriadicCube 2) (G : Vec 2 → Vec 2) :
    squareVectorEnergy Q (fun x => squareQuarterTurn (G x)) = squareVectorEnergy Q G := by
  unfold squareVectorEnergy
  simp only [Fin.sum_univ_two, squareQuarterTurn, Matrix.cons_val_zero, Matrix.cons_val_one,
    energy_eq_integral_sq, neg_sq]
  ring

/-- Almost-everywhere stream equality preserves every projected flux energy. -/
theorem squareProjection_stream_energy (Q : TriadicCube 2) {j : Vec 2 → Vec 2}
    (w : H1Function (openCubeSet Q))
    (hj : j =ᵐ[volume.restrict (openCubeSet Q)] (fun x => squareQuarterTurn (w.grad x))) (r : ℕ) :
    squareVectorEnergy Q (squareProjection Q r j) = squareVectorEnergy Q (squareProjection Q r w.grad) := by
  have heq : squareProjection Q r j = squareProjection Q r (fun x => squareQuarterTurn (w.grad x)) := by
    funext x i
    exact congrFun (square_scalar_projection_congr_ae Q r
      (hj.mono fun _ hx => congrFun hx i)) x
  rw [heq, squareProjection_quarterTurn, squareVectorEnergy_quarterTurn]

end ASDExplicitGamma.Cold
