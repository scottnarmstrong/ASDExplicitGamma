module

public import ASDExplicitGamma.Cold.PlateauOnSquare
public import ASDExplicitGamma.Cold.PlateauProfileMoments

/-! # Exact normalized moments of the native-square plateau -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The native plateau has every finite moment needed in the transport proof. -/
theorem memLp_plateauOnSquare (Q : TriadicCube 2) (p : ℝ≥0∞) :
    MemLp (plateauOnSquare Q) p (normalizedCubeMeasure Q) :=
  MemLp.of_bound (lipschitzWith_plateauOnSquare Q).continuous.aestronglyMeasurable
    (12 / 7) (Filter.Eventually.of_forall (norm_plateauOnSquare_le Q))

/-- The exact normalized first moment on every native square. -/
theorem integral_plateauOnSquare (Q : TriadicCube 2) :
    ∫ x, plateauOnSquare Q x ∂normalizedCubeMeasure Q = 1 := by
  apply integral_plateau_profile ((memLp_plateauOnSquare Q 2).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (Filter.Eventually.of_forall (plateauOnSquare_nonneg Q))
    (Filter.Eventually.of_forall (fun x => (le_abs_self _).trans (norm_plateauOnSquare_le Q x)))
  exact fun s hs hsM => plateauOnSquare_superlevel_measure Q hs hsM

/-- The exact normalized second moment on every native square. -/
theorem integral_plateauOnSquare_sq (Q : TriadicCube 2) :
    ∫ x, plateauOnSquare Q x ^ 2 ∂normalizedCubeMeasure Q = 66 / 49 := by
  apply integral_plateau_profile_sq (memLp_plateauOnSquare Q 2).integrable_sq
    (Filter.Eventually.of_forall (plateauOnSquare_nonneg Q))
    (Filter.Eventually.of_forall (fun x => (le_abs_self _).trans (norm_plateauOnSquare_le Q x)))
  exact fun s hs hsM => plateauOnSquare_superlevel_measure Q hs hsM

/-- The exact normalized squared fluctuation used by the affine/residual block. -/
theorem integral_plateauOnSquare_sub_one_sq (Q : TriadicCube 2) :
    ∫ x, (plateauOnSquare Q x - 1) ^ 2 ∂normalizedCubeMeasure Q = 17 / 49 := by
  have hi := (memLp_plateauOnSquare Q 2).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi2 := (memLp_plateauOnSquare Q 2).integrable_sq
  have hic : Integrable (fun _ : Vec 2 => (1 : ℝ)) (normalizedCubeMeasure Q) := integrable_const 1
  have heq : (fun x => (plateauOnSquare Q x - 1) ^ 2) =
      (fun x => plateauOnSquare Q x ^ 2 - 2 * plateauOnSquare Q x + 1) := by
    funext x; ring
  rw [heq, integral_add (f := fun x => plateauOnSquare Q x ^ 2 - 2 * plateauOnSquare Q x)
    (g := fun _ => 1) (hi2.sub (hi.const_mul 2)) hic,
    integral_sub (f := fun x => plateauOnSquare Q x ^ 2) (g := fun x => 2 * plateauOnSquare Q x)
      hi2 (hi.const_mul 2), integral_const_mul, integral_plateauOnSquare,
    integral_plateauOnSquare_sq, integral_const]
  norm_num [Measure.real, normalizedCubeMeasure_apply_univ]

end ASDExplicitGamma.Cold
