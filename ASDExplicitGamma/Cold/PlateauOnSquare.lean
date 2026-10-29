module

public import ASDExplicitGamma.Cold.PlateauWeakCutoff
public import ASDExplicitGamma.Cold.SquareVectorEnergy

/-! # The actual source plateau on a native triadic square -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- The closed spatial square corresponding to a native triadic cube. -/
def closedSquare (Q : TriadicCube 2) : Set (Vec 2) :=
  Icc (cubeCorner Q) (fun i => cubeCorner Q i + cubeScaleFactor Q)

/-- Coordinates in the source unit square. -/
def squareCoordinates (Q : TriadicCube 2) (x : Vec 2) : Vec 2 :=
  fun i => (x i - cubeCorner Q i) / cubeScaleFactor Q

/-- The source plateau, continuously extended by zero off its native square. -/
def plateauOnSquare (Q : TriadicCube 2) (x : Vec 2) : ℝ :=
  plateauZeroExtension (squareCoordinates Q x)

/-- The half-open native square and its closed representative have the same measure. -/
theorem cubeSet_ae_eq_closedSquare (Q : TriadicCube 2) :
    cubeSet Q =ᵐ[volume] closedSquare Q := by
  rw [cubeSet_eq_box]
  exact Measure.univ_pi_Ico_ae_eq_Icc

/-- Normalized measure can use the closed square without changing any integral. -/
theorem normalizedCubeMeasure_eq_closedSquare (Q : TriadicCube 2) :
    normalizedCubeMeasure Q = ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (closedSquare Q) := by
  rw [normalizedCubeMeasure, cubeMeasure, Measure.restrict_congr_set (cubeSet_ae_eq_closedSquare Q)]

/-- Points in the native closed square have coordinates in the source square. -/
theorem squareCoordinates_mem_unit {Q : TriadicCube 2} {x : Vec 2} (hx : x ∈ closedSquare Q) :
    squareCoordinates Q x ∈ plateauUnitSquare := by
  have hℓ := cubeScaleFactor_pos' Q
  constructor <;> intro i
  · exact div_nonneg (sub_nonneg.mpr (hx.1 i)) hℓ.le
  · apply (div_le_iff₀ hℓ).mpr
    linarith only [hx.2 i]

/-- On the native square, the definition is precisely P1's source formula. -/
theorem plateauOnSquare_eq {Q : TriadicCube 2} {x : Vec 2} (hx : x ∈ closedSquare Q) :
    plateauOnSquare Q x = plateauCutoff (squareCoordinates Q x) :=
  plateauZeroExtension_eq (squareCoordinates_mem_unit hx)

/-- The spatial coordinate map has the exact inverse-side-length Lipschitz bound. -/
theorem lipschitzWith_squareCoordinates (Q : TriadicCube 2) :
    LipschitzWith (NNReal.mk (cubeScaleFactor Q) (cubeScaleFactor_pos' Q).le)⁻¹
      (squareCoordinates Q) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have heq : squareCoordinates Q x - squareCoordinates Q y =
      (cubeScaleFactor Q)⁻¹ • (x - y) := by
    ext i
    simp only [squareCoordinates, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (cubeScaleFactor_pos' Q), dist_eq_norm]
  exact le_rfl

/-- The scale-correct global Lipschitz bound for the actual plateau. -/
theorem lipschitzWith_plateauOnSquare (Q : TriadicCube 2) :
    LipschitzWith ((48 / 7) * (NNReal.mk (cubeScaleFactor Q) (cubeScaleFactor_pos' Q).le)⁻¹)
      (plateauOnSquare Q) :=
  lipschitzWith_plateauZeroExtension.comp (lipschitzWith_squareCoordinates Q)

/-- The uniform value bound of the rescaled cutoff. -/
theorem norm_plateauOnSquare_le (Q : TriadicCube 2) (x : Vec 2) :
    ‖plateauOnSquare Q x‖ ≤ 12 / 7 :=
  norm_plateauZeroExtension_le _

/-- The actual spatial superlevel squares after scaling and translation. -/
theorem plateau_raw_square_superlevel (Q : TriadicCube 2) {s : ℝ}
    (hs : 0 ≤ s) (hsm : s ≤ 12 / 7) :
    {x : Vec 2 | s ≤ plateauCutoff (squareCoordinates Q x)} =
      Icc (fun i => cubeCorner Q i + cubeScaleFactor Q * (7 * s / 48))
        (fun i => cubeCorner Q i + cubeScaleFactor Q * (1 - 7 * s / 48)) := by
  have hℓ := cubeScaleFactor_pos' Q
  change (squareCoordinates Q) ⁻¹' {y : Vec 2 | s ≤ plateauCutoff y} = _
  rw [plateauCutoff_superlevel hs hsm]
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc, Pi.le_def, squareCoordinates]
  constructor
  · rintro ⟨hl, hu⟩
    constructor <;> intro i
    · have h := (le_div_iff₀ hℓ).mp (hl i)
      linarith only [h]
    · have h := (div_le_iff₀ hℓ).mp (hu i)
      linarith only [h]
  · rintro ⟨hl, hu⟩
    constructor <;> intro i
    · apply (le_div_iff₀ hℓ).mpr
      linarith only [hl i]
    · apply (div_le_iff₀ hℓ).mpr
      linarith only [hu i]

/-- Normalized measure is supported on the native closed square. -/
theorem ae_mem_closedSquare (Q : TriadicCube 2) :
    ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ closedSquare Q := by
  rw [normalizedCubeMeasure_eq_closedSquare]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

/-- Every raw nonnegative superlevel lies inside the native square. -/
theorem plateau_raw_square_superlevel_subset (Q : TriadicCube 2) {s : ℝ}
    (hs : 0 ≤ s) (hsm : s ≤ 12 / 7) :
    {x : Vec 2 | s ≤ plateauCutoff (squareCoordinates Q x)} ⊆ closedSquare Q := by
  rw [plateau_raw_square_superlevel Q hs hsm]
  intro x hx
  have hℓ := (cubeScaleFactor_pos' Q).le
  have hprod : 0 ≤ cubeScaleFactor Q * (7 * s / 48) := mul_nonneg hℓ (by positivity)
  constructor <;> intro i
  · linarith only [hx.1 i, hprod]
  · linarith only [hx.2 i, hprod]

/-- The exact source tail area is preserved under the native scaling. -/
theorem plateauOnSquare_superlevel_measure (Q : TriadicCube 2) {s : ℝ}
    (hs : 0 ≤ s) (hsm : s ≤ 12 / 7) :
    (normalizedCubeMeasure Q).real {x : Vec 2 | s ≤ plateauOnSquare Q x} =
      (1 - 7 * s / 24) ^ 2 := by
  have hcongr : (normalizedCubeMeasure Q) {x : Vec 2 | s ≤ plateauOnSquare Q x} =
      (normalizedCubeMeasure Q) {x : Vec 2 | s ≤ plateauCutoff (squareCoordinates Q x)} := by
    apply measure_congr
    filter_upwards [ae_mem_closedSquare Q] with x hx
    simp only [plateauOnSquare_eq hx]
  rw [Measure.real, hcongr]
  have hm : MeasurableSet {x : Vec 2 | s ≤ plateauCutoff (squareCoordinates Q x)} :=
    measurableSet_le measurable_const
      (continuous_plateauCutoff.comp (lipschitzWith_squareCoordinates Q).continuous).measurable
  rw [normalizedCubeMeasure_eq_closedSquare, Measure.smul_apply, Measure.restrict_apply hm,
    inter_eq_left.mpr (plateau_raw_square_superlevel_subset Q hs hsm),
    plateau_raw_square_superlevel Q hs hsm, Real.volume_Icc_pi]
  have hside : 0 ≤ 1 - 7 * s / 24 := by linarith only [hsm]
  have hprod : 0 ≤ cubeScaleFactor Q * (1 - 7 * s / 24) :=
    mul_nonneg (cubeScaleFactor_pos' Q).le hside
  have hcoord (i : Fin 2) :
      (cubeCorner Q i + cubeScaleFactor Q * (1 - 7 * s / 48)) -
        (cubeCorner Q i + cubeScaleFactor Q * (7 * s / 48)) =
      cubeScaleFactor Q * (1 - 7 * s / 24) := by ring
  simp only [hcoord, Fin.prod_univ_two, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_pos Q).le),
    ENNReal.toReal_ofReal hprod]
  unfold cubeVolume
  field_simp [(cubeScaleFactor_pos' Q).ne']

/-- Native square membership is exactly unit-square coordinate membership. -/
theorem squareCoordinates_mem_unit_iff (Q : TriadicCube 2) (x : Vec 2) :
    squareCoordinates Q x ∈ plateauUnitSquare ↔ x ∈ closedSquare Q := by
  constructor
  · intro hx
    have hℓ := cubeScaleFactor_pos' Q
    constructor <;> intro i
    · have h := (le_div_iff₀ hℓ).mp (hx.1 i)
      simpa only [zero_mul, sub_nonneg] using h
    · have h := (div_le_iff₀ hℓ).mp (hx.2 i)
      linarith only [h]
  · exact squareCoordinates_mem_unit

/-- The rescaled cutoff vanishes off its native closed square. -/
theorem plateauOnSquare_eq_zero_of_not_mem {Q : TriadicCube 2} {x : Vec 2}
    (hx : x ∉ closedSquare Q) : plateauOnSquare Q x = 0 := by
  apply plateauZeroExtension_eq_zero_of_not_mem
  exact fun h => hx ((squareCoordinates_mem_unit_iff Q x).mp h)

/-- The source cutoff's support is contained in the native closed square. -/
theorem tsupport_plateauOnSquare_subset (Q : TriadicCube 2) :
    tsupport (plateauOnSquare Q) ⊆ closedSquare Q := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (plateauOnSquare_eq_zero_of_not_mem hnot)

/-- The rescaled source cutoff is nonnegative everywhere. -/
theorem plateauOnSquare_nonneg (Q : TriadicCube 2) (x : Vec 2) :
    0 ≤ plateauOnSquare Q x := plateauZeroExtension_nonneg _

end ASDExplicitGamma.Cold
