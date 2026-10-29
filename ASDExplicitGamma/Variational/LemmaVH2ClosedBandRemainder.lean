module

public import ASDExplicitGamma.Variational.LemmaVDiag
public import ASDExplicitGamma.Variational.LemmaVH2Band
public import ASDExplicitGamma.Variational.LemmaVH2Remainder
public import ASDExplicitGamma.Triadic.PlanarDirectionVolume

/-! Closed source Lemma V for stationary-band and common-center remainder directions. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem lemmaV_diag_band (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (H : ℕ → ResponseCoefficient (openCubeSet (originCube 2 m)))
    (η : ℕ → PlanarW2Infinity (originCube 2 m))
    {ι : Type*} (sB : Finset ι) (vB LB : ι → ℝ)
    (hrep : RepresentsQ3Band η sB vB LB) (hv : ∀ k ∈ sB, 0 ≤ vB k) (hL : ∀ k ∈ sB, 0 < LB k)
    (hlink : ∀ l, (η l).value.toFun =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
      fun x => responseCoefficientExtension (H l) x / σ) :
    let Q := originCube 2 m
    let κ := lemmaVH2BandConstant (diagMeshRadius (originCube 2 m) j) (q3BandMoment sB vB LB 0) (q3BandMoment sB vB LB 2) (q3BandMoment sB vB LB 4)
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
    unfold κ lemmaVH2BandConstant lemmaVH2C1 lemmaVH2C2
    have hr := (diagMeshRadius_pos (originCube 2 m) j).le
    positivity
  exact lemmaV_diag m j ν σ hν hσ k H (fun l => (η l).value)
    (fun l => (η l).value_memLp_top) (fun l i => (η l).gradient_memLp_top_volume i)
    hlink κ hκ (fun p u t c _ => lemmaV_H2_band Q j η sB vB LB hrep hv hL p u t c)

 theorem lemmaV_diag_remainder (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (H : ℕ → ResponseCoefficient (openCubeSet (originCube 2 m)))
    (η : ℕ → PlanarW2Infinity (originCube 2 m))
    (vB LB : ℝ) (hrep : RepresentsQ3Remainder η vB LB (cubeCenter (originCube 2 m)))
    (hv : 0 ≤ vB) (hL : 0 < LB)
    (hlink : ∀ l, (η l).value.toFun =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
      fun x => responseCoefficientExtension (H l) x / σ) :
    let Q := originCube 2 m
    let κ := Real.sqrt vB*lemmaVH2Bn (cubeScaleFactor (originCube 2 m)/LB) (diagMeshRadius (originCube 2 m) j/LB)
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
    unfold κ lemmaVH2Bn lemmaVH2C1 lemmaVH2C2
    have hρ : 0 ≤ cubeScaleFactor (originCube 2 m)/LB := div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' _).le hL.le
    have hδ : 0 ≤ diagMeshRadius (originCube 2 m) j/LB := div_nonneg (diagMeshRadius_pos _ _).le hL.le
    positivity
  exact lemmaV_diag m j ν σ hν hσ k H (fun l => (η l).value)
    (fun l => (η l).value_memLp_top) (fun l i => (η l).gradient_memLp_top_volume i)
    hlink κ hκ (fun p u t c _ => lemmaV_H2_remainder Q j η vB LB hrep hv hL p u t c)

end
end ASDExplicitGamma.Variational
