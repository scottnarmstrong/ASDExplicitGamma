module

public import ASDExplicitGamma.Triadic.DiagMeshCorners
public import ASDExplicitGamma.Triadic.DiagNodalCorners
public import ASDExplicitGamma.Triadic.DiagAffine

/-! Identification of the actual source interpolant with its centered lattice polynomial. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization
open scoped BigOperators Fin.CommRing

noncomputable section

/-- Actual centered cell coefficients, obtained from the odd-reflected source means. -/
def diagSourceCellCoefficients (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) : Fin 4 → ℝ :=
  let instPeriodNonzero : NeZero (2*3^j) := ⟨by positivity⟩
  fun a => diagNodalCoefficients (diagPeriodLag (3^j)) (diagAxisLag 0) (diagAxisLag 1)
    (diagOddGrid (3^j) (diagSourceMeans Q j v)) a (diagPeriodEmbed k)

/-- Source nodal averages coincide with all four corners of the cell polynomial. -/
theorem diagInterpolant_h10_cell_corner (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) (b : Fin 2 → Fin 2) :
    (diagInterpolant Q j u.toH1Function).toFun (diagCellCorner (diagMeshCell Q j k) b) =
      diagBilinearPolynomial (diagMeshCell Q j k) (diagSourceCellCoefficients Q j u.toH1Function k)
        (diagCellCorner (diagMeshCell Q j k) b) := by
  let instPeriodNonzero : NeZero (2*3^j) := ⟨by positivity⟩
  let f := diagOddGrid (3^j) (diagSourceMeans Q j u.toH1Function)
  let c := diagSourceCellCoefficients Q j u.toH1Function k
  have hn : (diagInterpolant Q j u.toH1Function).toFun (diagCellCorner (diagMeshCell Q j k) b) =
      diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) (3^j)
        (cubeProjection Q j u.toH1Function.toFun) (diagMeshCornerIndex j k b) := by
    rw [diagMeshCell_corner_vertex, diagInterpolant_at_full_vertex,
      diagMeanGradient_h10, diagResidualLinear_h10]
    simp
  rw [hn, diagSourceNodes_at_cell_corner]
  have hc := diagNodalCoefficients_corner (diagPeriodLag (3^j)) (diagAxisLag 0)
    (diagAxisLag 1) f (diagPeriodEmbed k) (b 0) (b 1)
  rw [diagStencilAction_corner_pair] at hc
  dsimp only at hc
  have hz : diagPeriodEmbed k + diagPeriodBits (3^j) b =
      diagPeriodEmbed k + (if b 0 = 0 then 0 else diagPeriodLag (3^j) (diagAxisLag 0)) +
        (if b 1 = 0 then 0 else diagPeriodLag (3^j) (diagAxisLag 1)) := by
    rw [diagPeriodBits_axes, add_assoc]
  rw [hz]
  change _ = diagBilinearPolynomial (diagMeshCell Q j k) c (diagCellCorner (diagMeshCell Q j k) b)
  rw [← hc, diagBilinearPolynomial_explicit]
  simp only [diagCenteredCoordinate_corner]
  change c 0 + ((b 0).val-1/2)*c 1 + ((b 1).val-1/2)*c 2 +
    ((b 0).val-1/2)*((b 1).val-1/2)*c 3 = _
  ring

/-- The concrete H10 source interpolant has exactly the lattice cell polynomial
at every point of every closed source tile, including boundary cells. -/
theorem diagInterpolant_h10_cell_polynomial (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) :
    ∀ x : Vec 2,
      (∀ i, cubeCorner (diagMeshCell Q j k) i ≤ x i ∧
        x i ≤ cubeCorner (diagMeshCell Q j k) i+cubeScaleFactor (diagMeshCell Q j k)) →
      (diagInterpolant Q j u.toH1Function).toFun x =
        diagBilinearPolynomial (diagMeshCell Q j k) (diagSourceCellCoefficients Q j u.toH1Function k) x := by
  apply diagBilinear_eq_polynomial_of_corners
  · obtain ⟨A, B, C, D, h⟩ := diagInterpolant_bilinear_cell Q j u.toH1Function
      (fun i => ((k i).val : ℤ))
    refine ⟨A, B, C, D, ?_⟩
    intro x hx
    apply h x
    intro i
    have hl : cubeCorner Q i + ((k i).val : ℤ) * diagMeshRadius Q j =
        cubeCorner (diagMeshCell Q j k) i := by rw [diagMeshCell_corner]; simp
    have hu : cubeCorner Q i + (((k i).val : ℤ)+1) * diagMeshRadius Q j =
        cubeCorner (diagMeshCell Q j k) i+cubeScaleFactor (diagMeshCell Q j k) := by
      rw [diagMeshCell_corner, diagMeshCell_side]
      push_cast
      ring
    rw [hl, hu]
    exact hx i
  · exact diagInterpolant_h10_cell_corner Q j u k

end

end ASDExplicitGamma.Triadic
