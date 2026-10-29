module

public import ASDExplicitGamma.Variational.LemmaVH2Combination
public import ASDExplicitGamma.Variational.LemmaVH2RemainderDirections
public import ASDExplicitGamma.Variational.LemmaVH2RemainderConstants

/-! The common-center remainder H2 route, with every actual tile series. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

local instance lemmaVH2RemainderFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 theorem lemmaV_H2_remainder (Q : TriadicCube 2) (j : ℕ)
    (η : ℕ → PlanarW2Infinity Q) (v L : ℝ)
    (hrep : RepresentsQ3Remainder η v L (cubeCenter Q)) (hv : 0 ≤ v) (hL : 0 < L)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (t : Finset ℕ) (c : ℕ → ℝ) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ b, Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
      (cubeIncrement R (n+1) (fun x => lemmaVRowCombination I (fun l => (η l).value) φ t c x b)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I (fun l => (η l).value) φ t c)) ≤
      (Real.sqrt v*lemmaVH2Bn (cubeScaleFactor Q/L) (diagMeshRadius Q j/L))*Real.sqrt (∑ l ∈ t, c l^2)*
        Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro φ I
  let z := Real.sqrt (∑ l ∈ t, c l^2)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hval : ∀ᵐ x ∂normalizedCubeMeasure Q,
      |(PlanarW2Infinity.linearCombination η t c).value.toFun x| ≤
        Real.sqrt (v*(lemmaVH2R1/2)*(cubeScaleFactor Q/L)^2)*z := by
    filter_upwards [hilbert_ae_cubeSet Q] with x hx
    exact q3Remainder_direction_value_cap η v L hrep hv t c hx
  have hb := lemmaVH2_row_bound Q j (PlanarW2Infinity.linearCombination η t c) p u
    (mul_nonneg (Real.sqrt_nonneg _) hz) (mul_nonneg (Real.sqrt_nonneg _) hz)
    (mul_nonneg (Real.sqrt_nonneg _) hz) hval
    (Filter.Eventually.of_forall (q3Remainder_direction_gradient_cap η v L (cubeCenter Q) hrep hv t c))
    (Filter.Eventually.of_forall (q3Remainder_direction_hessian_cap η v L (cubeCenter Q) hrep hv hL t c))
  dsimp only at hb
  rw [← lemmaVRowCombination_linearCombination] at hb
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  rw [lemmaVH2RowConstant_scale, lemmaVH2RowConstant_remainder hv hL
    (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le]

end
end ASDExplicitGamma.Variational
