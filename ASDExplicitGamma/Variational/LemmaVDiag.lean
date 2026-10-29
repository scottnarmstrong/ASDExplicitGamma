module

public import ASDExplicitGamma.Variational.LemmaV
public import ASDExplicitGamma.Triadic.DiagInterpolant

/-! Lemma V for the concrete source DIAG cell-mean nodal interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic

noncomputable section

/-- Concrete Lemma V. The source DIAG map is fixed and its affine residual
property is proved. The only remaining family estimate is the source H2
row-form product bound, including the positive-series convergence it asserts. -/
theorem lemmaV_diag (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    let Q := originCube 2 m
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let I := diagInterpolant Q j
    ∀ (H : ℕ → ResponseCoefficient U) (η : ℕ → H1Function U),
      (∀ l, MemLp (η l) (⊤ : ENNReal) (volume.restrict U)) →
      (∀ l b, MemLp (fun x => (η l).grad x b) (⊤ : ENNReal) (volume.restrict U)) →
      (∀ l, (η l).toFun =ᵐ[volume.restrict U]
        fun x => responseCoefficientExtension (H l) x / σ) →
      ∀ κ : ℝ, 0 ≤ κ →
      (∀ p (r : H10Function U) (s : Finset ℕ) (c : ℕ → ℝ),
        (∑ l ∈ s, c l ^ 2) ≤ 1 →
        let v := lemmaVAffinePotential hU p r
        (∀ R ∈ descendantsAtDepth Q j, ∀ b,
          Summable (fun n => (Real.sqrt 3) ^ (n + 1) * energy R
            (cubeIncrement R (n + 1) (fun x => lemmaVRowCombination I η v s c x b)))) ∧
        Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I η v s c)) ≤
          κ * Real.sqrt (∑ l ∈ s, c l ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) →
      (∀ (s : Finset ℕ) (c : ℕ → ℝ), (∑ l ∈ s, c l ^ 2) ≤ 1 →
        |fderiv ℝ (lemmaVTrace m ν σ) k (∑ l ∈ s, c l • H l)| ≤
          2 * κ * lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) *
            Real.sqrt (lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4)) *
              Real.sqrt (∑ l ∈ s, c l ^ 2)) ∧
      Summable (fun l : ℕ => (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ∧
      (∑' l : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ≤
        4 * κ ^ 2 * (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
          lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  intro Q U hU I H η hη hDη hlink κ hκ hH2
  exact lemmaV_of_interpolant m j ν σ hν hσ k I H η hη hDη hlink
    (diagInterpolant_affine_residual_memH10 Q j) κ hκ hH2

end

end ASDExplicitGamma.Variational
