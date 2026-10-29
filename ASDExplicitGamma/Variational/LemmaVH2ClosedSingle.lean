module

public import ASDExplicitGamma.Variational.LemmaVDiag
public import ASDExplicitGamma.Variational.LemmaVH2Single
public import ASDExplicitGamma.Triadic.PlanarDirectionVolume

/-! Lemma V closed for the canonical covariance-defect direction. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem lemmaV_diag_single (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) {L : ℝ} (hL : 0 < L)
    (H : ℕ → ResponseCoefficient (openCubeSet (originCube 2 m)))
    (hlink : ∀ l, (q3CovarianceDefectFamily (originCube 2 m) L l).value.toFun
      =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
        fun x => responseCoefficientExtension (H l) x / σ) :
    let Q := originCube 2 m
    let κ := lemmaVH2kn (cubeScaleFactor Q/L) (diagMeshRadius Q j/L)
    (∀ (s : Finset ℕ) (c : ℕ → ℝ), (∑ l ∈ s, c l ^ 2) ≤ 1 →
        |fderiv ℝ (lemmaVTrace m ν σ) k (∑ l ∈ s, c l • H l)| ≤
          2 * κ * lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) *
            Real.sqrt (lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4)) *
              Real.sqrt (∑ l ∈ s, c l ^ 2)) ∧
      Summable (fun l : ℕ => (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ∧
      (∑' l : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ≤
        4 * κ ^ 2 * (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
          lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  intro Q κ
  have hκ : 0 ≤ κ := by
    unfold κ lemmaVH2kn lemmaVH2C1 lemmaVH2C2 lemmaVH2R1
    have hρ : 0 ≤ cubeScaleFactor Q/L := div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' _).le hL.le
    have hδ : 0 ≤ diagMeshRadius Q j/L := div_nonneg (diagMeshRadius_pos _ _).le hL.le
    positivity
  exact lemmaV_diag m j ν σ hν hσ k H (fun l => (q3CovarianceDefectFamily Q L l).value)
    (fun l => (q3CovarianceDefectFamily Q L l).value_memLp_top)
    (fun l i => (q3CovarianceDefectFamily Q L l).gradient_memLp_top_volume i)
    hlink κ hκ (fun p u t c _ => lemmaV_H2_single Q j hL p u t c)

end
end ASDExplicitGamma.Variational
