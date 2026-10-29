module

public import ASDExplicitGamma.Cold.SquareCutoffIBP

/-! # Actual H¹ transport and boundary forms, and their L² continuity -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- The actual cutoff transport form `⨍ φ ∇u · J∇w`, before volume normalization. -/
def squareTransportForm (Q : TriadicCube 2) (φ : Vec 2 → ℝ)
    (u w : H1Function (openCubeSet Q)) : ℝ :=
  -(∫ x in openCubeSet Q, φ x * u.grad x 0 * w.grad x 1) +
    ∫ x in openCubeSet Q, φ x * u.grad x 1 * w.grad x 0

/-- The actual integration-by-parts boundary-free form. -/
def squareTransportBoundaryForm (Q : TriadicCube 2) (φ : Vec 2 → ℝ)
    (u w : H1Function (openCubeSet Q)) : ℝ :=
  (∫ x in openCubeSet Q, lipschitzWeakGradient φ x 0 * u.toFun x * w.grad x 1) -
    ∫ x in openCubeSet Q, lipschitzWeakGradient φ x 1 * u.toFun x * w.grad x 0

/-- The transport form is an actual L² weighted pairing of weak gradient coordinates. -/
theorem squareTransportForm_eq_pairings (Q : TriadicCube 2) {φ : Vec 2 → ℝ}
    (hφ : MemLp φ ⊤ (volume.restrict (openCubeSet Q)))
    (u w : H1Function (openCubeSet Q)) :
    squareTransportForm Q φ u w =
      -weightedL2Pairing hφ (u.gradCoordToScalarL2 0) (w.gradCoordToScalarL2 1) +
        weightedL2Pairing hφ (u.gradCoordToScalarL2 1) (w.gradCoordToScalarL2 0) := by
  rw [weightedL2Pairing_eq_integral_of_ae hφ _ _ (u.coeFn_gradCoordToScalarL2 0)
    (w.coeFn_gradCoordToScalarL2 1),
    weightedL2Pairing_eq_integral_of_ae hφ _ _ (u.coeFn_gradCoordToScalarL2 1)
    (w.coeFn_gradCoordToScalarL2 0)]
  rfl

/-- The boundary form is an L² pairing of the function value and the other gradient. -/
theorem squareTransportBoundaryForm_eq_pairings (Q : TriadicCube 2) {φ : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (u w : H1Function (openCubeSet Q)) :
    squareTransportBoundaryForm Q φ u w =
      weightedL2Pairing (hφ.memLp_lineDeriv (μ := volume.restrict (openCubeSet Q)) (basisVec 0))
        u.toScalarL2 (w.gradCoordToScalarL2 1) -
      weightedL2Pairing (hφ.memLp_lineDeriv (μ := volume.restrict (openCubeSet Q)) (basisVec 1))
        u.toScalarL2 (w.gradCoordToScalarL2 0) := by
  rw [weightedL2Pairing_eq_integral_of_ae _ _ _ u.coeFn_toScalarL2 (w.coeFn_gradCoordToScalarL2 1),
    weightedL2Pairing_eq_integral_of_ae _ _ _ u.coeFn_toScalarL2 (w.coeFn_gradCoordToScalarL2 0)]
  rfl

/-- Strong L² convergence of weak gradients passes through the actual transport form. -/
theorem tendsto_squareTransportForm {ι : Type*} {l : Filter ι} (Q : TriadicCube 2)
    {φ : Vec 2 → ℝ} (hφ : MemLp φ ⊤ (volume.restrict (openCubeSet Q)))
    (M : ℝ) (hM : ∀ᵐ x ∂volume.restrict (openCubeSet Q), ‖φ x‖ ≤ M)
    {u w : ι → H1Function (openCubeSet Q)} {U W : H1Function (openCubeSet Q)}
    (hu : ∀ i, Tendsto (fun n => (u n).gradCoordToScalarL2 i) l (𝓝 (U.gradCoordToScalarL2 i)))
    (hw : ∀ i, Tendsto (fun n => (w n).gradCoordToScalarL2 i) l (𝓝 (W.gradCoordToScalarL2 i))) :
    Tendsto (fun n => squareTransportForm Q φ (u n) (w n)) l (𝓝 (squareTransportForm Q φ U W)) := by
  simp_rw [squareTransportForm_eq_pairings Q hφ]
  exact (tendsto_weightedL2Pairing hφ M hM (hu 0) (hw 1)).neg.add
    (tendsto_weightedL2Pairing hφ M hM (hu 1) (hw 0))

/-- Strong H¹ convergence passes through the integration-by-parts form with only a Lipschitz
cutoff. This uses its genuine measurable weak gradient and the global source Lipschitz bound. -/
theorem tendsto_squareTransportBoundaryForm {ι : Type*} {l : Filter ι} (Q : TriadicCube 2)
    {φ : Vec 2 → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ)
    {u w : ι → H1Function (openCubeSet Q)} {U W : H1Function (openCubeSet Q)}
    (hu : Tendsto (fun n => (u n).toScalarL2) l (𝓝 U.toScalarL2))
    (hw : ∀ i, Tendsto (fun n => (w n).gradCoordToScalarL2 i) l (𝓝 (W.gradCoordToScalarL2 i))) :
    Tendsto (fun n => squareTransportBoundaryForm Q φ (u n) (w n)) l
      (𝓝 (squareTransportBoundaryForm Q φ U W)) := by
  simp_rw [squareTransportBoundaryForm_eq_pairings Q hφ]
  have hB (i : Fin 2) : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      ‖lineDeriv ℝ φ x (basisVec i)‖ ≤ C * ‖basisVec i‖ :=
    Filter.Eventually.of_forall (fun _ => norm_lineDeriv_le_of_lipschitz ℝ hφ)
  exact (tendsto_weightedL2Pairing (hφ.memLp_lineDeriv (basisVec 0)) _ (hB 0) hu (hw 1)).sub
    (tendsto_weightedL2Pairing (hφ.memLp_lineDeriv (basisVec 1)) _ (hB 1) hu (hw 0))

/-- The smooth identity expressed in the same actual weak-gradient forms used in the limit. -/
theorem squareTransportForm_eq_boundary_of_smooth (Q : TriadicCube 2) {φ : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφs : tsupport φ ⊆ closedSquare Q)
    (hφtop : MemLp φ ⊤ (volume.restrict (openCubeSet Q)))
    (u w : H1Function (openCubeSet Q))
    (hu : ContDiff ℝ (⊤ : ℕ∞) u.toFun) (hw : ContDiff ℝ (⊤ : ℕ∞) w.toFun)
    (hug : ∀ x i, u.grad x i = smoothPartial u.toFun i x)
    (hwg : ∀ x i, w.grad x i = smoothPartial w.toFun i x) :
    squareTransportForm Q φ u w = squareTransportBoundaryForm Q φ u w := by
  have hi0 : Integrable (fun x => φ x * u.grad x 0 * w.grad x 1)
      (volume.restrict (openCubeSet Q)) := (hφtop.mul (r := 2) (u.gradMemL2 0)).integrable_mul (w.gradMemL2 1)
  have hi1 : Integrable (fun x => φ x * u.grad x 1 * w.grad x 0)
      (volume.restrict (openCubeSet Q)) := (hφtop.mul (r := 2) (u.gradMemL2 1)).integrable_mul (w.gradMemL2 0)
  have h := square_cutoff_ibp_smooth Q hφ hφs hu hw
  simp_rw [← hug, ← hwg] at h
  have hl : (fun x => φ x * (-(u.grad x 0 * w.grad x 1) + u.grad x 1 * w.grad x 0)) =
      (fun x => -(φ x * u.grad x 0 * w.grad x 1) + φ x * u.grad x 1 * w.grad x 0) := by funext x; ring
  have hr : (fun x => lipschitzWeakGradient φ x 0 * (-(u.toFun x * w.grad x 1))) =
      (fun x => -(lipschitzWeakGradient φ x 0 * u.toFun x * w.grad x 1)) := by funext x; ring
  have hr1 : (fun x => lipschitzWeakGradient φ x 1 * (u.toFun x * w.grad x 0)) =
      (fun x => lipschitzWeakGradient φ x 1 * u.toFun x * w.grad x 0) := by funext x; ring
  rw [hl, integral_add (f := fun x => -(φ x * u.grad x 0 * w.grad x 1))
    (g := fun x => φ x * u.grad x 1 * w.grad x 0) hi0.neg hi1, integral_neg, hr, integral_neg, hr1] at h
  unfold squareTransportForm squareTransportBoundaryForm
  linarith only [h]

end ASDExplicitGamma.Cold
