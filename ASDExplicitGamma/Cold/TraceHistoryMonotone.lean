module

public import ASDExplicitGamma.Cold.ColdPlateauFamily
public import ASDExplicitGamma.Cold.FiniteTraceMaximum

/-! # Monotonicity of the actual depthwise trace maxima -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- The actual projection identity gives trace subadditivity on every source partition. -/
theorem square_trace_subadditive (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (v : SquareMatchedOptimizers Q a)
    {r : ℕ} (f : ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val a) :
    traceDefect (openCubeSet Q) a 1 ≤ squareCellMean Q r (fun R => traceDefect (openCubeSet R.val) a 1) := by
  have h := squareCellMean_mono Q r (fun R => squareMatchedCellResidual_nonneg Q hEll v f R)
  rw [squareCellMean_const,squareMatchedCellResidual_mean] at h
  linarith only [h]

/-- Each source generation is inhabited. -/
instance instColdSquareCellsNonempty (Q : TriadicCube 2) (r : ℕ) : Nonempty (SquareCells Q r) := by
  obtain ⟨R,hR⟩ := descendantsAtDepth_nonempty Q r
  exact ⟨⟨R,hR⟩⟩

/-- The literal actual trace maximum at depth r in one fixed coefficient/frame. -/
def ColdPlateauFamily.traceMaximum {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (r : ℕ) (ω : Ω) : ℝ :=
  coldFiniteMaximum (fun R : SquareCells Q r => (F.atDepth r).cellTrace R) ω

/-- Nonnegativity comes from actual coarse duality at every source cell. -/
theorem ColdPlateauFamily.traceMaximum_nonneg {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (r : ℕ) (ω : Ω) : 0 ≤ F.traceMaximum r ω := by
  obtain ⟨R,hR⟩ := coldFiniteMaximum_eq_some (fun R : SquareCells Q r => (F.atDepth r).cellTrace R) ω
  change 0 ≤ coldFiniteMaximum _ ω
  rw [hR]
  exact coarse_square_traceDefect_nonneg R.val
    ((F.elliptic ω).mono (measurableSet_openCubeSet R.val) (openCubeSet_subset_of_mem_descendantsAtDepth R.property))

/-- Actual depthwise maxima are nondecreasing by the proved trace subadditivity.
No stochastic independence or assumed history monotonicity is used. -/
theorem ColdPlateauFamily.traceMaximum_mono {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (ω : Ω) : Monotone (fun r => F.traceMaximum r ω) := by
  apply monotone_nat_of_le_succ
  intro r
  obtain ⟨R,hR⟩ := coldFiniteMaximum_eq_some (fun R : SquareCells Q r => (F.atDepth r).cellTrace R) ω
  change coldFiniteMaximum _ ω ≤ _
  rw [hR]
  let hER := (F.elliptic ω).mono (measurableSet_openCubeSet R.val)
    (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
  have hchild (S : SquareCells R.val 1) : S.val ∈ descendantsAtDepth Q (r+1) := by
    rw [mem_descendantsAtDepth_succ_iff]
    exact ⟨R.val,R.property,by simpa only [descendantsAtDepth_one] using S.property⟩
  let f := fun S : SquareCells R.val 1 => F.cells (r+1) ω ⟨S.val,hchild S⟩
  have hsub := square_trace_subadditive R.val hER (F.cells r ω R) f
  have hm := squareCellMean_mono R.val 1 (fun S : SquareCells R.val 1 =>
    le_coldFiniteMaximum (fun S : SquareCells Q (r+1) => (F.atDepth (r+1)).cellTrace S) ω ⟨S.val,hchild S⟩)
  rw [squareCellMean_const] at hm
  exact hsub.trans hm

end ASDExplicitGamma.Cold
