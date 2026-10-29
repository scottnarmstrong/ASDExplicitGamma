module

public import ASDExplicitGamma.Main.EuclideanMeanValue
public import ASDExplicitGamma.Triadic.DiagCoordinate

/-! The exact cube second-distance moment used by the centered q3 source. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators

/-- Euclidean distance to a fixed point has an exact normalized cube moment. -/
theorem main_cube_distance_moment (Q : TriadicCube 2) (x : Vec 2) :
    (∫ y, mainSpatialDistanceSq x y ∂normalizedCubeMeasure Q) =
      cubeScaleFactor Q^2*(∑ i : Fin 2, ((diagCenteredCoordinate Q i x)^2+1/12)) := by
  have hR := (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).ne'
  have he (i : Fin 2) (y : Vec 2) : (x i-y i)^2 = cubeScaleFactor Q^2*
      ((diagCenteredCoordinate Q i x)^2-
        2*diagCenteredCoordinate Q i x*diagCenteredCoordinate Q i y+
        (diagCenteredCoordinate Q i y)^2) := by
    unfold diagCenteredCoordinate
    field_simp
    ring
  unfold mainSpatialDistanceSq
  rw [integral_finsetSum]
  · rw [Finset.mul_sum Finset.univ (fun i : Fin 2 => (diagCenteredCoordinate Q i x)^2+1/12) (cubeScaleFactor Q^2)]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [he i]
    rw [integral_const_mul]
    have hc := (diagCenteredCoordinate_memLp Q i).integrable (by norm_num : (1:ENNReal) ≤ 2)
    have hs := (diagCenteredCoordinate_memLp Q i).integrable_sq
    have hc' : Integrable (fun y => (diagCenteredCoordinate Q i x)^2-
        2*diagCenteredCoordinate Q i x*diagCenteredCoordinate Q i y) (normalizedCubeMeasure Q) :=
      (integrable_const _).sub (hc.const_mul _)
    rw [integral_add hc' hs,
      integral_sub (integrable_const _) (hc.const_mul _), integral_const_mul,
      integral_const, ← cubeAverage_eq_integral_normalizedCubeMeasure,
      diagCenteredCoordinate_mean, mul_zero, sub_zero,
      ← energy_eq_integral_sq, diagCenteredCoordinate_energy]
    simp only [Measure.real_def, normalizedCubeMeasure_apply_univ, ENNReal.toReal_one, one_smul]
  · intro i _
    have hcont : Continuous (fun y : Vec 2 => x i-y i) := by fun_prop
    exact ((main_continuous_memLp_top Q hcont).mono_exponent (by simp : (2:ENNReal) ≤ ⊤)).integrable_sq

/-- At every physical point of the cube, the moment is at most 2R²/3. -/
theorem main_cube_distance_moment_le (Q : TriadicCube 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    (∫ y, mainSpatialDistanceSq x y ∂normalizedCubeMeasure Q) ≤ (2/3)*cubeScaleFactor Q^2 := by
  rw [main_cube_distance_moment]
  have hR := ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q
  have hb (i : Fin 2) : (diagCenteredCoordinate Q i x)^2 ≤ (1/4:ℝ) := by
    have hi := hx i
    have hi' : cubeCorner Q i ≤ x i ∧ x i < cubeCorner Q i+cubeScaleFactor Q := by
      dsimp [cubeCorner]
      constructor
      · exact hi.1
      · nlinarith only [hi.2]
    have hd0 : 0 ≤ (x i-cubeCorner Q i)/cubeScaleFactor Q := div_nonneg (sub_nonneg.mpr hi'.1) hR.le
    have hd1 : (x i-cubeCorner Q i)/cubeScaleFactor Q ≤ 1 :=
      (div_le_one hR).2 (by linarith only [hi'.2])
    unfold diagCenteredCoordinate
    nlinarith only [hd0, hd1]
  have hs : (∑ i : Fin 2, ((diagCenteredCoordinate Q i x)^2+1/12)) ≤ (2/3:ℝ) := by
    simp only [Fin.sum_univ_two]
    linarith only [hb 0, hb 1]
  exact (mul_le_mul_of_nonneg_left hs (sq_nonneg _)).trans_eq (mul_comm _ _)

end ASDExplicitGamma.Main
