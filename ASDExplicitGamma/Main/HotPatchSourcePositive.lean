module

public import ASDExplicitGamma.Main.HotPatchRow
public import ASDExplicitGamma.Main.HotPatchSourceBound
public import ASDExplicitGamma.Scalar.FlatSourceHaarLimit

/-! Hot-patch source: coordinatewise positive Haar series summability on each source cell and
summability of the per-cell source energy over the fresh modes. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Native

/-- On the open cell, the second block of the hot source is the quarter turn of minus the
corresponding coordinate vector of the hot row. -/
theorem hot_source_tile_coord_eq (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (P : BlockVec 2) (s : Finset whiteBasisIndex) (l : s)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (x : Vec 2)
    (hx : x ∈ openCubeSet U) :
    let w := hotPatchPotential Q depth nu sigma hnu hsigma k P
    let φU := oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
    let C1 := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q depth w.toH1Function
    let C2 := hotRowCorrectorPart s b L U φU
    (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2 =
      planarQuarterTurn (fun i => -((C1 x + C2 x).ofLp (l, i))) := by
  intro w φU C1 C2
  classical
  let I := diagInterpolant Q depth
  let φ := hotGluedCorrector Q depth nu sigma hnu hsigma k P
  let η := (mainQ3DirectionW2 Q b L (whiteBasis l)).value
  have hvalue (x : Vec 2) : η.toFun x =
      q3Convolution b L h3Zero (whiteBasis l) x := by
    rw [mainQ3DirectionW2_value]
  have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i =
      (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) x) (basisVec i) := by
    have hj := mainQ3DirectionW2_jet Q b L (whiteBasis l) (.first i) x
    change (mainQ3DirectionW2 Q b L (whiteBasis l)).value.grad x i =
      q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis l) x at hj
    have hderiv : (fderiv ℝ (q3Convolution b L h3Zero
        (whiteBasis l)) x) (basisVec i) =
        q3Convolution b L (mainQ3JetIndex (.first i))
          (whiteBasis l) x := by
      rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
      fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
        Model.Q3SpatialJet.count]
    exact hj.trans hderiv.symm
  let F : Vec 2 → Fin 2 → ℝ := fun x i =>
    η.toFun x * (I w.toH1Function).grad x i -
      η.grad x i * (w.toH1Function - I w.toH1Function).toFun x -
      η.grad x i * φU.toH1Function.toFun x
  have hcoord (x : Vec 2) (i : Fin 2) : (C1 x + C2 x).ofLp (l, i) = F x i := by
    have h1 := pureFluxMainQ3FiniteRawRow_coordinate_hotcopy whiteBasis s b L Q depth
      w.toH1Function l i x
    simp only [C1, C2, hotRowCorrectorPart, PiLp.add_apply, PiLp.smul_apply,
      mainQ3FiniteColumn, smul_eq_mul] at h1 ⊢
    rw [h1]
    simp only [F]
    rw [hvalue, hgrad]
    ring
  have hφ : φ.toH1Function x = φU.toH1Function x :=
    hot_glued_corrector_cell Q depth nu sigma hnu hsigma k P U hU x hx
  have e1 := congrFun (lemmaVH2_rowField_eq I η w.toH1Function) x
  have e2 := congrFun (lemmaVH2_rowField_eq
    (0 : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) η φ.toH1Function) x
  simp only [hotPatchSource, oldSignedLocalizedPotentialShear, Prod.snd_add]
  rw [e1, e2]
  funext i
  fin_cases i <;>
    simp [planarQuarterTurn, hcoord, F, hφ] <;> ring

/-- Coordinatewise positive Haar series of the hot source converge on every source cell. -/
theorem hot_source_positive_series (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (j : Fin 2) :
    Summable (fun d : ℕ => (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
      (fun x => -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2 j)))) := by
  classical
  let w := hotPatchPotential Q depth nu sigma hnu hsigma k P
  let φU := oldSignedCellFirstCorrector Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  let s : Finset whiteBasisIndex := {n}
  let l : s := ⟨n, Finset.mem_singleton_self n⟩
  have htri := hot_row_tile_triangle Q depth w s U hU b L φU
  have hmem := htri.1
  have hsum := htri.2.1
  let C : Vec 2 → EuclideanSpace ℝ (s × Fin 2) := fun x =>
    pureFluxMainQ3FiniteRawRow whiteBasis s b L Q depth w.toH1Function x +
      hotRowCorrectorPart s b L U φU x
  have hcoord (i : Fin 2) := main_hilbert_coordinate_summable U hmem hsum (l, i)
  have hsrc : ∀ x ∈ openCubeSet U,
      (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2 =
        planarQuarterTurn (fun i => -((C x).ofLp (l, i))) :=
    fun x hx => hot_source_tile_coord_eq Q depth nu sigma hnu hsigma k b L P s l U hU x hx
  fin_cases j
  · have hae : (fun x => -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2
        (0 : Fin 2))) =ᵐ[normalizedCubeMeasure U] (fun x => -((C x).ofLp (l, 1))) := by
      apply hot_ae_cube_of_open U
      intro x hx
      have h0 := congrFun (hsrc x hx) 0
      have h1 : (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2 0 =
          (C x).ofLp (l, 1) := by
        have : (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2 0 =
            planarQuarterTurn (fun i => -((C x).ofLp (l, i))) 0 := h0
        simp only [planarQuarterTurn, if_true] at this
        change _ = _ at this
        simpa using this
      show -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2 0) = _
      rw [h1]
    refine (hcoord 1).congr (fun d => ?_)
    have hterm : energy U (cubeIncrement U (d + 1)
        (fun x => -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2
          (0 : Fin 2)))) =
        energy U (cubeIncrement U (d + 1) (fun x => (C x).ofLp (l, 1))) := by
      rw [ASDExplicitGamma.Scalar.cubeIncrement_congr_ae U (d + 1) hae]
      simp only [Triadic.cubeIncrement_neg, Triadic.energy_neg]
    exact congrArg (fun y => (Real.sqrt 3) ^ (d + 1) * y) hterm.symm
  · have hae : (fun x => -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2
        (1 : Fin 2))) =ᵐ[normalizedCubeMeasure U] (fun x => (C x).ofLp (l, 0)) := by
      apply hot_ae_cube_of_open U
      intro x hx
      have h0 := congrFun (hsrc x hx) 1
      have h1 : (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2 1 =
          -((C x).ofLp (l, 0)) := by
        have : (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2 1 =
            planarQuarterTurn (fun i => -((C x).ofLp (l, i))) 1 := h0
        simpa [planarQuarterTurn] using this
      show -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2 1) = _
      rw [h1]
      ring
    refine (hcoord 0).congr (fun d => ?_)
    have hterm : energy U (cubeIncrement U (d + 1)
        (fun x => -((hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P x).2
          (1 : Fin 2)))) =
        energy U (cubeIncrement U (d + 1) (fun x => (C x).ofLp (l, 0))) := by
      rw [ASDExplicitGamma.Scalar.cubeIncrement_congr_ae U (d + 1) hae]
    exact congrArg (fun y => (Real.sqrt 3) ^ (d + 1) * y) hterm.symm

/-- Per-cell summability of the hot source energy over the fresh modes. -/
theorem hot_source_cell_summable (m : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 m) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) depth) :
    Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
      vectorPositiveHaarNorm U (fun x =>
        (hotPatchSource (originCube 2 m) depth depth nu sigma hnu hsigma k b L n
          (blockBasis c) x).2) ^ 2) := by
  classical
  obtain ⟨hs, -⟩ := hot_source_size_bound m depth nu sigma hnu hsigma k b L hL
  have hcard : (0 : ℝ) < ((descendantsAtDepth (originCube 2 m) depth).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨U, hU⟩
  refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun c _ => sq_nonneg _)
    (fun n => ?_) (hs.mul_left ((descendantsAtDepth (originCube 2 m) depth).card : ℝ))
  simp only [vectorPositiveHaarNorm]
  have hterm : ∀ c : BlockCoord 2, Real.sqrt (vectorPositiveHaarEnergy U (fun x =>
        (hotPatchSource (originCube 2 m) depth depth nu sigma hnu hsigma k b L n
          (blockBasis c) x).2)) ^ 2 ≤ ((descendantsAtDepth (originCube 2 m) depth).card : ℝ) *
      descendantsAverage (originCube 2 m) depth (fun V => vectorPositiveHaarEnergy V (fun x =>
        (hotPatchSource (originCube 2 m) depth depth nu sigma hnu hsigma k b L n
          (blockBasis c) x).2)) := by
    intro c
    rw [Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
    show _ ≤ _ * (((descendantsAtDepth (originCube 2 m) depth).card : ℝ)⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul]
    exact Finset.single_le_sum (f := fun V => vectorPositiveHaarEnergy V (fun x =>
        (hotPatchSource (originCube 2 m) depth depth nu sigma hnu hsigma k b L n
          (blockBasis c) x).2)) (fun V _ => vectorPositiveHaarEnergy_nonneg _ _) hU
  calc _ ≤ ∑ c : BlockCoord 2, _ := Finset.sum_le_sum fun c _ => hterm c
    _ = _ := by rw [← Finset.mul_sum]

end ASDExplicitGamma.Inverse
