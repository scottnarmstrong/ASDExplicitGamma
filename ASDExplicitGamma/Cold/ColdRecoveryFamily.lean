module

public import ASDExplicitGamma.Cold.SquareMatchedCutoff

/-! # The source random coefficient and actual matched optimizers used in cutoff recovery -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- Actual source data at one coefficient/frame, on a parent and its own depth-r cells.
All fields concern coefficients and genuine variational maximizers, not energy estimates. -/
structure ColdRecoveryFamily (Q : TriadicCube 2) (r : ℕ) (Ω : Type*) where
  coefficient : Ω → CoeffField 2
  lower : Ω → ℝ
  upper : Ω → ℝ
  elliptic : ∀ ω, IsEllipticFieldOn (lower ω) (upper ω) (openCubeSet Q) (coefficient ω)
  parent : ∀ ω, SquareMatchedOptimizers Q (coefficient ω)
  cells : ∀ ω, ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val (coefficient ω)

/-- The ordinary source parent trace defect in its fixed normalized coefficient/frame. -/
def ColdRecoveryFamily.parentTrace {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    (F : ColdRecoveryFamily Q r Ω) (ω : Ω) : ℝ := traceDefect (openCubeSet Q) (F.coefficient ω) 1

/-- The ordinary source trace defect on an actual own cell. -/
def ColdRecoveryFamily.cellTrace {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    (F : ColdRecoveryFamily Q r Ω) (R : SquareCells Q r) (ω : Ω) : ℝ :=
  traceDefect (openCubeSet R.val) (F.coefficient ω) 1

/-- The actual cutoff-weighted parent energy. -/
def ColdRecoveryFamily.parentCutoffEnergy {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    (F : ColdRecoveryFamily Q r Ω) (ω : Ω) : ℝ :=
  volumeAverage (openCubeSet Q) (fun x => plateauOnSquare Q x*squareMatchedDensity Q (F.parent ω) x)

/-- The actual parent-cutoff-weighted energy on an own cell. -/
def ColdRecoveryFamily.cellCutoffEnergy {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    (F : ColdRecoveryFamily Q r Ω) (R : SquareCells Q r) (ω : Ω) : ℝ :=
  volumeAverage (openCubeSet R.val) (fun x => plateauOnSquare Q x*squareMatchedDensity R.val (F.cells ω R) x)

/-- Ordinary integrability of the source quantities whose expectations occur in P4. -/
structure ColdRecoveryIntegrable {Q : TriadicCube 2} {r : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (F : ColdRecoveryFamily Q r Ω) (ℙ : Measure Ω) : Prop where
  parentTrace : Integrable F.parentTrace ℙ
  cellTrace : ∀ R, Integrable (F.cellTrace R) ℙ
  parentCutoffEnergy : Integrable F.parentCutoffEnergy ℙ
  cellCutoffEnergy : ∀ R, Integrable (F.cellCutoffEnergy R) ℙ

/-- The actual depth-four own-cell cutoff comparison before expectation. -/
theorem ColdRecoveryFamily.cellCutoffEnergy_lower {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    (F : ColdRecoveryFamily Q r Ω) (hr : r = 4) (R : SquareCells Q r) (ω : Ω) :
    2*(cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ))*F.cellTrace R ω ≤ F.cellCutoffEnergy R ω := by
  let hER := (F.elliptic ω).mono (measurableSet_openCubeSet R.val)
    (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
  have hd := integrable_squareMatchedDensity R.val hER (F.cells ω R)
  have hw := integrable_plateau_squareMatchedDensity Q R.val hER (F.cells ω R)
  let b := cubeAverage R.val (plateauOnSquare Q)-(1/8 : ℝ)
  have h := square_volumeAverage_mono_ae R.val (hd.const_mul b) hw (show
      (fun x => b*squareMatchedDensity R.val (F.cells ω R) x) ≤ᵐ[volume.restrict (openCubeSet R.val)]
      (fun x => plateauOnSquare Q x*squareMatchedDensity R.val (F.cells ω R) x) from by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R.val)] with x hx
    exact mul_le_mul_of_nonneg_right
      (plateau_depth_four_average_le R.property hr (openCubeSet_subset_cubeSet R.val hx))
      (squareMatchedDensity_nonneg R.val hER (F.cells ω R) hx))
  have heq : (fun x => b*squareMatchedDensity R.val (F.cells ω R) x) =
      b • squareMatchedDensity R.val (F.cells ω R) := rfl
  rw [heq,volumeAverage_smul,squareMatchedDensity_average R.val hER] at h
  change b*(2*F.cellTrace R ω) ≤ F.cellCutoffEnergy R ω at h
  dsimp [b] at h
  nlinarith only [h]

end ASDExplicitGamma.Cold
