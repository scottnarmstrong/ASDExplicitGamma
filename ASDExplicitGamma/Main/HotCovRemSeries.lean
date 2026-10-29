module

public import ASDExplicitGamma.Main.HotCovRem
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry
public import ASDExplicitGamma.Triadic.DiagEnergyCongr

/-! MA-E-COVARIANCE, step 12: each residual hot source mode has genuine convergent
positive Haar increments on every tile (needed for K/P duality). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar ASDExplicitGamma.Native
  ASDExplicitGamma.Inverse
open scoped BigOperators

noncomputable section

theorem hot_cov_rem_positive_series (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d) (c : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) * energy U (cubeIncrement U (j + 1)
      (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n P U x c))) := by
  classical
  let s : Finset whiteBasisIndex := {n}
  let w := hotPatchPotential Q d nu sigma hnu hsigma k P
  let φU := oldSignedCellFirstCorrector Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  let φ0 := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 w
  have hφ0 : φ0 = w.toH1Function := ASDExplicitGamma.Native.old_signed_zero_affine_potential Q w
  let C1 := mainQ3DiagResidualColumn whiteBasis s b L Q d φ0 U
  let C2 := hotRowCorrectorPart s b L U φU
  let C : Vec 2 → EuclideanSpace ℝ (s × Fin 2) := fun x => C1 x + C2 x
  have hA : MemLp C1 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    rintro ⟨l, i⟩
    simpa only [C1, mainQ3DiagResidualColumn_coordinate] using
      main_q3_residual_coordinate_memLp whiteBasis b L Q d φ0 U hU l i
  have hPA := (main_q3_diag_residual_local whiteBasis s b L Q d 0 w U hU).1
  have hB : MemLp C2 2 (normalizedCubeMeasure U) := by
    let Mcol := mainRankOneMultiplier U (mainQ3FiniteColumn whiteBasis s b L)
      (mainQ3FiniteColumn_contDiff whiteBasis s b L)
    have hBpos := Mcol.product_memLp φU.toH1Function.memL2_normalizedCubeMeasure
    have hneg := hBpos.neg
    convert hneg using 1
    funext x
    simp [C2, hotRowCorrectorPart, Mcol, mainRankOneMultiplier, neg_smul]
  have hCol := main_q3_negative_column_h1_product whiteBasis s b L U φU.toH1Function
  have hAdd := main_hilbert_positive_add U hA hB hPA hCol.1
  have hmem : MemLp C 2 (normalizedCubeMeasure U) := hA.add hB
  have hsum := hAdd.1
  let F : Vec 2 → Fin 2 → ℝ := fun x i =>
    (hotCovPsi b L n x - cubeAverage U (hotCovPsi b L n)) *
        hotCovZ Q d nu sigma hnu hsigma k P x i -
      hotCovPsiGrad b L n i x *
        (w.toH1Function - diagInterpolant Q d w.toH1Function).toFun x -
      hotCovPsiGrad b L n i x * φU.toH1Function.toFun x
  have hcoord (x : Vec 2) (i : Fin 2) : (C x).ofLp (⟨n, by simp [s]⟩, i) = F x i := by
    have h1 := mainQ3DiagResidualColumn_coordinate whiteBasis s b L Q d φ0 U
      ⟨n, by simp [s]⟩ x i
    simp only [C, C1, C2, hotRowCorrectorPart, PiLp.add_apply, PiLp.smul_apply,
      mainQ3FiniteColumn, smul_eq_mul, WithLp.ofLp_toLp] at h1 ⊢
    rw [h1]
    simp only [F, mainQ3ResidualCoordinate, hφ0, hotCovZ, hotCovPsi, hotCovPsiGrad]
    ring
  have hFser (i : Fin 2) : Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => -F x i))) := by
    have h := main_hilbert_coordinate_summable U hmem hsum (⟨n, by simp [s]⟩, i)
    have hf : (fun x => (C x).ofLp (⟨n, by simp [s]⟩, i)) = fun x => F x i := by
      funext x
      exact hcoord x i
    rw [hf] at h
    simp_rw [cubeIncrement_neg, energy_neg]
    exact h
  have hQ := positive_series_quarterTurn U (fun x i => -F x i) hFser c
  have hae : (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n P U x c) =ᵐ[
      volume.restrict (cubeSet U)] (fun x => planarQuarterTurn (fun i => -F x i) c) := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet U]
    refine (ae_restrict_iff' (measurableSet_openCubeSet U)).2 (Filter.Eventually.of_forall ?_)
    intro x hx
    have := hot_cov_rem_cell_formula Q d nu sigma hnu hsigma k b L n P U hU x hx
    show hotCovRem Q d nu sigma hnu hsigma k b L n P U x c = _
    rw [this]
  simp_rw [diagCubeIncrement_congr_ae U _ hae]
  exact hQ

end

end ASDExplicitGamma.Main
