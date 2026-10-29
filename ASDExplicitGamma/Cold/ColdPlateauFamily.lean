module

public import ASDExplicitGamma.Cold.PlateauFineTail

/-! # One fixed coefficient and optimizer family across all plateau depths -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- One actual terminal family, with its own matched optimizers at every cell depth.
The coefficient and parent optimizers are shared literally across all depths. -/
structure ColdPlateauFamily (Q : TriadicCube 2) (Ω : Type*) where
  coefficient : Ω → CoeffField 2
  lower : Ω → ℝ
  upper : Ω → ℝ
  elliptic : ∀ ω, IsEllipticFieldOn (lower ω) (upper ω) (openCubeSet Q) (coefficient ω)
  parent : ∀ ω, SquareMatchedOptimizers Q (coefficient ω)
  cells : ∀ r, ∀ ω, ∀ R : SquareCells Q r, SquareMatchedOptimizers R.val (coefficient ω)

/-- The same actual family viewed at a specified depth. -/
def ColdPlateauFamily.atDepth {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (r : ℕ) : ColdRecoveryFamily Q r Ω where
  coefficient := F.coefficient
  lower := F.lower
  upper := F.upper
  elliptic := F.elliptic
  parent := F.parent
  cells := F.cells r

/-- The actual projected graph at one depth. -/
def ColdPlateauFamily.projectedGraph {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (r : ℕ) (ω : Ω) : ℝ :=
  squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r

/-- Every actual projected graph is nonnegative. -/
theorem ColdPlateauFamily.projectedGraph_nonneg {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (r : ℕ) (ω : Ω) : 0 ≤ F.projectedGraph r ω := by
  have h := squareCellMean_mono Q r (fun R => squareFourGraphEnergy_nonneg R.val
    (fun i => squareCellRestriction Q (F.elliptic ω) ((F.parent ω).primal i) R)
    (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField (F.elliptic ω))
      ((F.parent ω).adjoint i) R))
  rw [squareCellMean_const] at h
  exact h

/-- The all-depth source history controls each actual projected graph. -/
theorem ColdPlateauFamily.projectedGraph_history_bound {Q : TriadicCube 2} {Ω : Type*}
    (F : ColdPlateauFamily Q Ω) (r : ℕ) (ω : Ω) {D : ℝ} (hD : 0 ≤ D)
    (hroot : (F.atDepth r).parentTrace ω ≤ D)
    (hmax : ∀ R, (F.atDepth r).cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D) :
    F.projectedGraph r ω ≤ (8+6*(3:ℝ)^((r:ℝ)/4))*(1+D^2) := by
  have hgram := square_projected_graph_gram Q (F.elliptic ω) (η := 1) (by norm_num)
    (F.parent ω) r hmax
  have hn := coarse_square_traceDefect_nonneg Q (F.elliptic ω)
  have hs : 0 ≤ (3:ℝ)^((r:ℝ)/4) := Real.rpow_nonneg (by norm_num) _
  have hm := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 2*(1+(1:ℝ))+(2+1/(4*(1:ℝ)))*((3:ℝ)^((r:ℝ)/4)*D) by positivity)
  change _ ≤ _*(2*(F.atDepth r).parentTrace ω) at hgram
  have hd : 2*D ≤ 1+D^2 := by nlinarith only [sq_nonneg (D-1)]
  have h := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 4)
  have hsq := mul_nonneg hs (sq_nonneg D)
  norm_num at hgram hm
  dsimp only [ColdPlateauFamily.projectedGraph]
  nlinarith only [hgram,hm,h,hsq,hs]

end ASDExplicitGamma.Cold
