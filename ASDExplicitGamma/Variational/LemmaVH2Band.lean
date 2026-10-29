module

public import ASDExplicitGamma.Variational.LemmaVH2Combination
public import ASDExplicitGamma.Variational.LemmaVH2BandDirections

/-! The stationary-band H2 route, with every actual tile series included. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

local instance lemmaVH2BandFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 theorem lemmaV_H2_band {ι : Type*} (Q : TriadicCube 2) (j : ℕ)
    (η : ℕ → PlanarW2Infinity Q) (s : Finset ι) (v L : ι → ℝ)
    (hrep : RepresentsQ3Band η s v L) (hv : ∀ k ∈ s, 0 ≤ v k) (hL : ∀ k ∈ s, 0 < L k)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (t : Finset ℕ) (c : ℕ → ℝ) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ b, Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
      (cubeIncrement R (n+1) (fun x => lemmaVRowCombination I (fun l => (η l).value) φ t c x b)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I (fun l => (η l).value) φ t c)) ≤
      lemmaVH2BandConstant (diagMeshRadius Q j) (q3BandMoment s v L 0)
        (q3BandMoment s v L 2) (q3BandMoment s v L 4)*Real.sqrt (∑ l ∈ t, c l^2)*
          Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro φ I
  let z := Real.sqrt (∑ l ∈ t, c l^2)
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hb := lemmaVH2_row_bound Q j (PlanarW2Infinity.linearCombination η t c) p u
    (mul_nonneg (Real.sqrt_nonneg _) hz) (mul_nonneg (Real.sqrt_nonneg _) hz)
    (mul_nonneg (Real.sqrt_nonneg _) hz)
    (Filter.Eventually.of_forall (q3Band_direction_value_cap η s v L hrep t c))
    (Filter.Eventually.of_forall (q3Band_direction_gradient_cap η s v L hrep hv hL t c))
    (Filter.Eventually.of_forall (q3Band_direction_hessian_cap η s v L hrep hv hL t c))
  dsimp only at hb
  rw [← lemmaVRowCombination_linearCombination] at hb
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  unfold lemmaVH2RowConstant lemmaVH2BandConstant
  ring

end
end ASDExplicitGamma.Variational
