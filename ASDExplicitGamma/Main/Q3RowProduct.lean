module

public import ASDExplicitGamma.Main.Q3RowCaps
public import ASDExplicitGamma.Variational.LemmaVH2Combination

/-! Actual q3 covariance row products with the source planar triple. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped BigOperators

local instance mainQ3RowFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The row coefficient retains the sharp operator moments. -/
noncomputable def mainQ3RowConstant (r b L : ℝ) : ℝ :=
  Real.sqrt (b^2) + r*(36/25)*Real.sqrt ((78/5)*b^2/L^2) +
    r^2*(57/200)*Real.sqrt ((23244/25)*b^2/L^4)

/-- The actual covariance row and affine-data DIAG map obey the source
triple (1,1.440,.285). Every jet covariance cap is internally discharged.
The result is uniform over finite Gaussian row combinations. -/
theorem main_q3_row_product {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (j : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (s : Finset ι) (c : ι → ℝ) :
    let η := fun l => mainQ3DirectionW2 Q b L (e l)
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy R
      (cubeIncrement R (k+1) (fun x => lemmaVRowCombination I (fun l => (η l).value) φ s c x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I (fun l => (η l).value) φ s c)) ≤
      mainQ3RowConstant (diagMeshRadius Q j) b L.1*Real.sqrt (∑ l ∈ s, c l^2)*
        Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro η φ I
  have hb := lemmaVH2_row_bound Q j (PlanarW2Infinity.linearCombination η s c) p u
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall (main_q3_row_value_cap e Q b L s c))
    (Filter.Eventually.of_forall (main_q3_row_gradient_cap e Q b L s c))
    (Filter.Eventually.of_forall (main_q3_row_hessian_cap e Q b L s c))
  dsimp only at hb
  rw [← lemmaVRowCombination_linearCombination] at hb
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  unfold lemmaVH2RowConstant mainQ3RowConstant lemmaVH2C1 lemmaVH2C2
  ring

end ASDExplicitGamma.Main
