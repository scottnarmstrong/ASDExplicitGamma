module

public import ASDExplicitGamma.Main.HotPatchSourcePositive
public import ASDExplicitGamma.Main.HotEOscillationPathwise
public import ASDExplicitGamma.Main.HotPatchTrial
public import ASDExplicitGamma.Native.OldSignedGlobalOldSourceEnergy

/-! The patched-residual energy of the hot-patched source (the source-square group of
the hot trial) is bounded by the cell average of `B_U s_U²`, with `s_U` the complete positive
size of the hot source on the cell. Generic-source copy of
`old_signed_global_old_source_energy_bill`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

theorem hot_cell_residual_congr (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F F' : Vec 2 → BlockVec 2) (h : F = F')
    (hF : MemBlockL2 (openCubeSet Q) F) (hF' : MemBlockL2 (openCubeSet Q) F') :
    oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF =
      oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F' hF' := by
  subst h
  rfl

theorem hot_source_eq_zero_second (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) :
    hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P =
      fun x => (0, (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2) := by
  funext x
  apply Prod.ext
  · simp [hotPatchSource, oldSignedLocalizedPotentialShear]
  · rfl

/-- Sharp cellwise energy bound for the hot source. -/
theorem hot_source_cell_energy_le (mm : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 mm) depth) :
    let Q := originCube 2 mm
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let F := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P
    let R := oldSignedCellResidual Q U hsub nu sigma hnu hsigma k F
      (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n P)
    oldSignedEnergyPairing U nu sigma kU R R ≤
      oldSignedInverseHistory U a * vectorPositiveHaarNorm U (fun x => (F x).2) ^ 2 := by
  intro Q hsub a kU F R
  let g := fun x => (F x).2
  have hFparent := hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n P
  have hFeq : F = fun x => (0, g x) :=
    hot_source_eq_zero_second Q depth nu sigma hnu hsigma k b L n P
  have hF0 : MemBlockL2 (openCubeSet Q) (fun x => (0, g x)) := by
    rw [← hFeq]
    exact hFparent
  have hF : MemBlockL2 (openCubeSet U) (fun x => (0, g x)) :=
    hF0.mono_measure (Measure.restrict_mono_set volume hsub)
  have hp : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) * energy U
      (cubeIncrement U (j + 1) (fun x => g x i))) := by
    intro i
    refine (hot_source_positive_series Q depth nu sigma hnu hsigma k b L n P U hU i).congr
      fun d => ?_
    simp only [Triadic.cubeIncrement_neg, Triadic.energy_neg]
    rfl
  have he := old_signed_pure_second_sharp_energy U nu sigma hnu hsigma kU g hF hp
  have hres : R = scalarResidualField U nu sigma hnu hsigma kU (toHilbertBlockL2OfBlockField hF) := by
    have := hot_cell_residual_congr Q U hsub nu sigma hnu hsigma k F (fun x => (0, g x)) hFeq
      hFparent hF0
    simp only [R, this]
    rfl
  have hs := old_signed_cell_histories Q U hsub nu sigma hnu hsigma k
  dsimp only at he
  rw [hs.1] at he
  rw [hres]
  exact he

theorem hot_source_family_eq (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) :
    (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).source n =
      ∑ c : BlockCoord 2, oldSignedEnergyPairing Q nu sigma k
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
          (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))
          (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis c)))
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
          (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))
          (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))) :=
  rfl

/-- The patched-residual energy of the hot source, summed over modes and loads, is summable and
bounded by the cell average of `B_U s_U²`. -/
theorem hot_source_energy_bill (mm : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 mm))) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 mm) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1) :
    let Q := originCube 2 mm
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n => (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).source n
    Summable f ∧ (∑' n, f n) ≤ descendantsAverage Q depth (fun U =>
      oldSignedInverseHistory U a * hotSourceSize (fun n P x =>
        hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U ^ 2) := by
  classical
  intro Q a f
  let fc := fun (n : whiteBasisIndex) (U : OldSignedCellIndex Q depth) =>
    let R := fun c => oldSignedCellResidual Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) nu sigma hnu hsigma k
      (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))
      (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))
    ∑ c : BlockCoord 2, oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) (R c) (R c)
  have he : f = (fun n => oldSignedCellAverage Q depth (fc n)) := by
    funext n
    show (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).source n = _
    rw [hot_source_family_eq]
    simp_rw [old_signed_local_residual_cell_pairing]
    rw [old_signed_cell_average_sum]
  have hcell : ∀ U : OldSignedCellIndex Q depth,
      Summable (fun n => fc n U) ∧
        (∑' n, fc n U) ≤ oldSignedInverseHistory U.val a *
          hotSourceSize (fun n P x =>
            hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U.val ^ 2 := by
    intro U
    have hU := U.property
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let p := fun (n : whiteBasisIndex) (c : BlockCoord 2) => vectorPositiveHaarNorm U.val
      (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2)
    have hps : Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2, p n c ^ 2) :=
      hot_source_cell_summable mm depth nu sigma hnu hsigma k b L hL U.val hU
    have hB : 0 ≤ oldSignedInverseHistory U.val a :=
      lemmaVInverseHistory_nonneg U.val a (Real.one_lt_rpow (by norm_num) (by norm_num))
    have hE (n : whiteBasisIndex) : 0 ≤ fc n U := by
      apply Finset.sum_nonneg
      intro c _
      have hR : MemBlockL2 (openCubeSet U.val) (oldSignedCellResidual Q U.val hsub nu sigma hnu
        hsigma k (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))
        (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n (blockBasis c))) :=
        Lp.memLp _
      rw [← old_signed_energy_inner_fields U.val nu sigma hnu hsigma
        (oldSignedCellCoefficient Q U.val hsub k) hR hR]
      exact real_inner_self_nonneg
    have hpoint (n : whiteBasisIndex) : fc n U ≤
        oldSignedInverseHistory U.val a * ∑ c : BlockCoord 2, p n c ^ 2 := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
        hot_source_cell_energy_le mm depth nu sigma hnu hsigma k b L n (blockBasis c) U.val hU)
      simpa only [← Finset.mul_sum] using hh
    have hEs := (hps.mul_left (oldSignedInverseHistory U.val a)).of_nonneg_of_le hE hpoint
    have hEt := hEs.tsum_le_tsum hpoint (hps.mul_left (oldSignedInverseHistory U.val a))
    rw [tsum_mul_left] at hEt
    have hd0 : 0 ≤ ∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, p n c ^ 2 :=
      tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hdeq : hotSourceSize (fun n P x =>
        hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x) U.val ^ 2 =
        ∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, p n c ^ 2 := Real.sq_sqrt hd0
    exact ⟨hEs, by rw [hdeq]; exact hEt⟩
  rw [he, ← old_signed_cell_average_eq_descendantsAverage]
  exact old_signed_cell_average_series_upper Q depth fc _
    (fun U => (hcell U).1) (fun U => (hcell U).2)

end

end ASDExplicitGamma.Main
