module

public import ASDExplicitGamma.Main.HotCovSourceCell
public import ASDExplicitGamma.Main.HotPatchSourceBound
public import ASDExplicitGamma.Main.Q3RemainderCaps
public import ASDExplicitGamma.Main.Q3DiagResidualEstimate
public import ASDExplicitGamma.Main.Q3ResidualCoordinates

/-! MA-E-COVARIANCE, step 3: the residual hot source.  After the frozen part
`-a_{n,U} J ∇Iw` is removed, the remainder `rem` of the hot source on a tile is
paid by `κ_rem K(∇w)` (centered covariance residual columns) and
`k_d K(∇φ)` (the local-corrector column). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar ASDExplicitGamma.Native
  ASDExplicitGamma.Inverse
open scoped BigOperators

noncomputable section

local instance hotCovRemFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The residual source `f' - f⁰` on the tile `U`, where `f⁰ = -a_{n,U} J ∇Iw`
freezes the mode at its cell mean. -/
def hotCovRem (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2) (x : Vec 2) : Vec 2 :=
  (hotPatchSource Q d d nu sigma hnu hsigma k b L n P x).2 +
    cubeAverage U (hotCovPsi b L n) •
      planarQuarterTurn (hotCovZ Q d nu sigma hnu hsigma k P x)

/-- Pointwise form of the residual on an open cell. -/
theorem hot_cov_rem_cell_formula (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d)
    (x : Vec 2) (hx : x ∈ openCubeSet U) :
    hotCovRem Q d nu sigma hnu hsigma k b L n P U x =
      planarQuarterTurn (fun i => -((hotCovPsi b L n x - cubeAverage U (hotCovPsi b L n)) *
          hotCovZ Q d nu sigma hnu hsigma k P x i -
        hotCovPsiGrad b L n i x *
          ((hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function -
            diagInterpolant Q d (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function).toFun x -
        hotCovPsiGrad b L n i x *
          (oldSignedCellFirstCorrector Q U
            (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
            (fun _ => P) (memLp_const P)).toH1Function.toFun x)) := by
  unfold hotCovRem
  rw [hot_cov_source_cell_formula Q d nu sigma hnu hsigma k b L n P U hU x hx]
  funext i
  fin_cases i <;> simp [planarQuarterTurn] <;> ring

/-- On one tile, the residual source energy summed over a finite family of modes is
the Hilbert positive energy of the centered residual column plus the corrector
column. -/
theorem hot_cov_rem_tile_energy_eq (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (P : BlockVec 2) (s : Finset whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d) :
    let w := hotPatchPotential Q d nu sigma hnu hsigma k P
    let φU := oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
    let φ0 := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 w
    let C1 := mainQ3DiagResidualColumn whiteBasis s b L Q d φ0 U
    let C2 := hotRowCorrectorPart s b L U φU
    ∑ l ∈ s, vectorPositiveHaarEnergy U (fun x => hotCovRem Q d nu sigma hnu hsigma k b L l P U x) =
      hilbertPrimalEnergy U (Real.sqrt 3) (fun x => C1 x + C2 x) := by
  intro w φU φ0 C1 C2
  classical
  have hφ0 : φ0 = w.toH1Function := ASDExplicitGamma.Native.old_signed_zero_affine_potential Q w
  let C : Vec 2 → EuclideanSpace ℝ (s × Fin 2) := fun x => C1 x + C2 x
  have htri : MemLp C 2 (normalizedCubeMeasure U) ∧
      Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
        (hilbertCubeIncrement U (k+1) (fun x => C1 x + C2 x))) := by
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
    exact ⟨hA.add hB, hAdd.1⟩
  have hmem := htri.1
  have hsum := htri.2
  have hrow (l : s) :
      vectorPositiveHaarEnergy U (fun x =>
        hotCovRem Q d nu sigma hnu hsigma k b L l P U x) =
      ∑ i : Fin 2, primalEnergy U (Real.sqrt 3) (fun x => (C x).ofLp (l, i)) := by
    let F : Vec 2 → Fin 2 → ℝ := fun x i =>
      (hotCovPsi b L l x - cubeAverage U (hotCovPsi b L l)) *
          hotCovZ Q d nu sigma hnu hsigma k P x i -
        hotCovPsiGrad b L l i x *
          (w.toH1Function - diagInterpolant Q d w.toH1Function).toFun x -
        hotCovPsiGrad b L l i x * φU.toH1Function.toFun x
    have hcoord (x : Vec 2) (i : Fin 2) : (C x).ofLp (l, i) = F x i := by
      have h1 := mainQ3DiagResidualColumn_coordinate whiteBasis s b L Q d φ0 U l x i
      simp only [C, C1, C2, hotRowCorrectorPart, PiLp.add_apply, PiLp.smul_apply,
        mainQ3FiniteColumn, smul_eq_mul, WithLp.ofLp_toLp] at h1 ⊢
      rw [h1]
      simp only [F, mainQ3ResidualCoordinate, hφ0, hotCovZ, hotCovPsi, hotCovPsiGrad]
      ring
    have hsrc (x : Vec 2) (hx : x ∈ openCubeSet U) :
        hotCovRem Q d nu sigma hnu hsigma k b L l P U x =
          planarQuarterTurn (fun i => -F x i) :=
      hot_cov_rem_cell_formula Q d nu sigma hnu hsigma k b L l P U hU x hx
    calc vectorPositiveHaarEnergy U (fun x =>
          hotCovRem Q d nu sigma hnu hsigma k b L l P U x)
        = vectorPositiveHaarEnergy U (fun x => planarQuarterTurn (fun i => -F x i)) := by
          unfold vectorPositiveHaarEnergy
          apply Finset.sum_congr rfl
          intro i _
          apply hot_primalEnergy_congr_open
          intro x hx
          exact congrFun (hsrc x hx) i
      _ = vectorPositiveHaarEnergy U (fun x i => -F x i) :=
          main_vectorPositiveHaarEnergy_quarterTurn U (fun x i => -F x i)
      _ = ∑ i : Fin 2, primalEnergy U (Real.sqrt 3) (fun x => (C x).ofLp (l, i)) := by
          unfold vectorPositiveHaarEnergy
          apply Finset.sum_congr rfl
          intro i _
          have hf : (fun x => (C x).ofLp (l, i)) = fun x => F x i := by
            funext x
            exact hcoord x i
          rw [hf]
          exact primalEnergy_neg U (Real.sqrt 3) (fun x => F x i)
  calc ∑ l ∈ s, vectorPositiveHaarEnergy U (fun x =>
        hotCovRem Q d nu sigma hnu hsigma k b L l P U x)
      = ∑ l : s, vectorPositiveHaarEnergy U (fun x =>
        hotCovRem Q d nu sigma hnu hsigma k b L l P U x) :=
        (Finset.sum_coe_sort s _).symm
    _ = ∑ l : s, ∑ i : Fin 2, primalEnergy U (Real.sqrt 3) (fun x => (C x).ofLp (l, i)) := by
        apply Finset.sum_congr rfl
        intro l _
        exact hrow l
    _ = hilbertPrimalEnergy U (Real.sqrt 3) C := by
        symm
        rw [main_hilbertPrimalEnergy_euclidean U hmem hsum, Fintype.sum_prod_type]

/-- The tile-averaged positive energy of the residual hot source, for every finite
family `s` of fresh modes and each constant load `P`:
`d_rem ≤ κ_rem K(∇w) + k_d K(∇φ)`. -/
theorem hot_cov_rem_load_energy_finset (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1)
    (P : BlockVec 2) (s : Finset whiteBasisIndex) :
    Real.sqrt (∑ l ∈ s, descendantsAverage Q d (fun U => vectorPositiveHaarEnergy U
      (fun x => hotCovRem Q d nu sigma hnu hsigma k b L l P U x))) ≤
      mainKrem (b ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q d
        (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad) +
      mainKd (b ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q d
        (hotGluedCorrector Q d nu sigma hnu hsigma k P).toH1Function.grad) := by
  classical
  let w := hotPatchPotential Q d nu sigma hnu hsigma k P
  let φ := hotGluedCorrector Q d nu sigma hnu hsigma k P
  let φ0 := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 w
  have hφ0 : φ0 = w.toH1Function := ASDExplicitGamma.Native.old_signed_zero_affine_potential Q w
  let E : TriadicCube 2 → ℝ := fun U => ∑ l ∈ s, vectorPositiveHaarEnergy U
    (fun x => hotCovRem Q d nu sigma hnu hsigma k b L l P U x)
  let F1 : TriadicCube 2 → ℝ := fun U =>
    hilbertPrimalEnergy U (Real.sqrt 3) (mainQ3DiagResidualColumn whiteBasis s b L Q d φ0 U)
  let K : TriadicCube 2 → ℝ := fun U => vectorWeakHaarEnergy U
    (fun x i => φ.toH1Function.grad x i)
  have hkd : 0 ≤ mainKd (b ^ 2) := mainKd_nonneg (b ^ 2)
  have hE0 (U : TriadicCube 2) (_ : U ∈ descendantsAtDepth Q d) : 0 ≤ E U :=
    Finset.sum_nonneg fun l _ => vectorPositiveHaarEnergy_nonneg U _
  have hF0 (U : TriadicCube 2) (_ : U ∈ descendantsAtDepth Q d) : 0 ≤ F1 U := by
    unfold F1 hilbertPrimalEnergy
    apply add_nonneg (hilbertEnergy_nonneg U _)
    exact tsum_nonneg fun k => mul_nonneg (by positivity) (hilbertEnergy_nonneg U _)
  have hK0 (U : TriadicCube 2) (_ : U ∈ descendantsAtDepth Q d) : 0 ≤ K U :=
    vectorWeakHaarEnergy_nonneg U _
  have hb (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d) :
      Real.sqrt (E U) ≤ 1 * Real.sqrt (F1 U) + mainKd (b ^ 2) * Real.sqrt (K U) +
        0 * Real.sqrt (K U) := by
    let φU := oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
    have hE := hot_cov_rem_tile_energy_eq Q d nu sigma hnu hsigma k b L P s U hU
    dsimp only at hE
    have hA : MemLp (mainQ3DiagResidualColumn whiteBasis s b L Q d φ0 U) 2
        (normalizedCubeMeasure U) := by
      apply memLp_piLp_iff.mpr
      rintro ⟨l, i⟩
      simpa only [mainQ3DiagResidualColumn_coordinate] using
        main_q3_residual_coordinate_memLp whiteBasis b L Q d φ0 U hU l i
    have hPA := (main_q3_diag_residual_local whiteBasis s b L Q d 0 w U hU).1
    have hB : MemLp (hotRowCorrectorPart s b L U φU) 2 (normalizedCubeMeasure U) := by
      let Mcol := mainRankOneMultiplier U (mainQ3FiniteColumn whiteBasis s b L)
        (mainQ3FiniteColumn_contDiff whiteBasis s b L)
      have hBpos := Mcol.product_memLp φU.toH1Function.memL2_normalizedCubeMeasure
      have hneg := hBpos.neg
      convert hneg using 1
      funext x
      simp [hotRowCorrectorPart, Mcol, mainRankOneMultiplier, neg_smul]
    have hCol := main_q3_negative_column_h1_product whiteBasis s b L U φU.toH1Function
    have hAdd := main_hilbert_positive_add U hA hB hPA hCol.1
    have htri : Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3) (fun x =>
        mainQ3DiagResidualColumn whiteBasis s b L Q d φ0 U x +
          hotRowCorrectorPart s b L U φU x)) ≤
        Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3)
          (mainQ3DiagResidualColumn whiteBasis s b L Q d φ0 U)) +
        Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3) (hotRowCorrectorPart s b L U φU)) := by
      simpa only [hilbertPositiveHaarNorm] using hAdd.2
    have hcol := hot_row_corrector_energy_le s b L U φU
    have hkdU : mainQ3ColumnConstant (cubeScaleFactor U) b L.1 ≤ mainKd (b ^ 2) :=
      mainQ3ColumnConstant_le_mainKd (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' U) (hL U hU)
    have hKeq := hot_corrector_cell_weak_energy_eq Q d nu sigma hnu hsigma k P U hU
    have hC2 : Real.sqrt (hilbertPrimalEnergy U (Real.sqrt 3) (hotRowCorrectorPart s b L U φU)) ≤
        mainKd (b ^ 2) * Real.sqrt (K U) := by
      have hR := (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' U).le
      have hcc : 0 ≤ mainQ3ColumnConstant (cubeScaleFactor U) b L.1 := by
        unfold mainQ3ColumnConstant
        positivity
      have h1 := Real.sqrt_le_sqrt hcol
      rw [Real.sqrt_sq (mul_nonneg hcc (by unfold vectorWeakHaarNorm; exact Real.sqrt_nonneg _))] at h1
      refine h1.trans ?_
      have : vectorWeakHaarNorm U (fun x i => φU.toH1Function.grad x i) = Real.sqrt (K U) := by
        unfold vectorWeakHaarNorm
        rw [hKeq]
      rw [this]
      exact mul_le_mul_of_nonneg_right hkdU (Real.sqrt_nonneg _)
    simp only [one_mul, zero_mul, add_zero]
    rw [show E U = _ from hE]
    exact htri.trans (add_le_add le_rfl hC2)
  have hagg := sqrt_descendantsAverage_energy_bound_three Q d E F1 K K
    (A := 1) (B := mainKd (b ^ 2)) (C := 0) (by norm_num) hkd le_rfl hE0 hF0 hK0 hK0 hb
  have hAvgE : descendantsAverage Q d E = ∑ l ∈ s, descendantsAverage Q d (fun U =>
      vectorPositiveHaarEnergy U
        (fun x => hotCovRem Q d nu sigma hnu hsigma k b L l P U x)) :=
    main_descendantsAverage_finset_sum Q d s _
  have hres := (main_q3_diag_residual_estimate whiteBasis s b L Q d 0 w).2
  have hgrad : (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 w).grad =
      w.toH1Function.grad := congrArg H1Function.grad hφ0
  rw [hgrad] at hres
  have hKr : mainQ3RemainderExact (diagMeshRadius Q d) b L.1 ≤ mainKrem (b ^ 2) :=
    (mainQ3RemainderExact_le (diagMeshRadius_pos Q d).le).trans
      (mainQ3RemainderConstant_le_mainKrem (diagMeshRadius_pos Q d) hmesh)
  have hK : descendantsAverage Q d K = lemmaVTiledWeakEnergy Q d
      (hotGluedCorrector Q d nu sigma hnu hsigma k P).toH1Function.grad := rfl
  rw [hK] at hagg
  rw [← hAvgE]
  calc Real.sqrt (descendantsAverage Q d E) ≤ _ := hagg
    _ ≤ _ := by
      simp only [one_mul, zero_mul, add_zero]
      refine add_le_add ?_ le_rfl
      refine hres.trans (mul_le_mul_of_nonneg_right hKr (Real.sqrt_nonneg _))

/-- The residual hot source over all fresh modes and the four canonical loads:
summable tile-averaged positive energy, with size
`d_rem ≤ κ_rem K(∇w) + k_d K(∇φ)` in the four-load tiled weak norms. -/
theorem hot_cov_rem_size_bound (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1) :
    let src : whiteBasisIndex → ℝ := fun n => ∑ c : BlockCoord 2,
      descendantsAverage Q d (fun U => vectorPositiveHaarEnergy U (fun x =>
        hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U x))
    Summable src ∧
    Real.sqrt (∑' n, src n) ≤
      mainKrem (b ^ 2) *
          Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
            (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) +
        mainKd (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
          (hotGluedCorrector Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) := by
  intro src
  classical
  let α := mainKrem (b ^ 2)
  let β := mainKd (b ^ 2)
  let x : BlockCoord 2 → ℝ := fun c => lemmaVTiledWeakEnergy Q d
    (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad
  let y : BlockCoord 2 → ℝ := fun c => lemmaVTiledWeakEnergy Q d
    (hotGluedCorrector Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad
  let srcc : whiteBasisIndex → BlockCoord 2 → ℝ := fun n c =>
    descendantsAverage Q d (fun U => vectorPositiveHaarEnergy U (fun x =>
      hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U x))
  have hα : 0 ≤ α := mainKrem_nonneg (b ^ 2)
  have hβ : 0 ≤ β := mainKd_nonneg (b ^ 2)
  have hx0 (c : BlockCoord 2) : 0 ≤ x c :=
    descendantsAverage_nonneg Q d _ (fun U _ => vectorWeakHaarEnergy_nonneg U _)
  have hy0 (c : BlockCoord 2) : 0 ≤ y c :=
    descendantsAverage_nonneg Q d _ (fun U _ => vectorWeakHaarEnergy_nonneg U _)
  have hs0 (n : whiteBasisIndex) (c : BlockCoord 2) : 0 ≤ srcc n c :=
    descendantsAverage_nonneg Q d _ (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hn (n : whiteBasisIndex) : 0 ≤ src n :=
    Finset.sum_nonneg fun c _ => hs0 n c
  have hfin (s : Finset whiteBasisIndex) :
      ∑ n ∈ s, src n ≤ (α * Real.sqrt (∑ c, x c) + β * Real.sqrt (∑ c, y c)) ^ 2 := by
    have hload (c : BlockCoord 2) : ∑ n ∈ s, srcc n c ≤
        α ^ 2 * x c + 2 * α * β * (Real.sqrt (x c) * Real.sqrt (y c)) + β ^ 2 * y c := by
      have h := hot_cov_rem_load_energy_finset Q d nu sigma hnu hsigma k b L hL hmesh
        (blockBasis c) s
      have hsum0 : 0 ≤ ∑ n ∈ s, srcc n c := Finset.sum_nonneg fun n _ => hs0 n c
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rw [Real.sq_sqrt hsum0] at h2
      refine h2.trans (le_of_eq ?_)
      have hxs := Real.sq_sqrt (hx0 c)
      have hys := Real.sq_sqrt (hy0 c)
      calc (α * Real.sqrt (x c) + β * Real.sqrt (y c)) ^ 2
          = α ^ 2 * (Real.sqrt (x c)) ^ 2 + 2 * α * β * (Real.sqrt (x c) * Real.sqrt (y c)) +
            β ^ 2 * (Real.sqrt (y c)) ^ 2 := by ring
        _ = _ := by rw [hxs, hys]
    calc ∑ n ∈ s, src n = ∑ c, ∑ n ∈ s, srcc n c := by
          simp only [src]
          rw [Finset.sum_comm]
      _ ≤ ∑ c, (α ^ 2 * x c + 2 * α * β * (Real.sqrt (x c) * Real.sqrt (y c)) + β ^ 2 * y c) :=
          Finset.sum_le_sum fun c _ => hload c
      _ = α ^ 2 * (∑ c, x c) + 2 * α * β * (∑ c, Real.sqrt (x c) * Real.sqrt (y c)) +
            β ^ 2 * (∑ c, y c) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ α ^ 2 * (∑ c, x c) + 2 * α * β * (Real.sqrt (∑ c, x c) * Real.sqrt (∑ c, y c)) +
            β ^ 2 * (∑ c, y c) := by
          have hcs : ∑ c, Real.sqrt (x c) * Real.sqrt (y c) ≤
              Real.sqrt (∑ c, (Real.sqrt (x c)) ^ 2) * Real.sqrt (∑ c, (Real.sqrt (y c)) ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
          simp only [Real.sq_sqrt (hx0 _), Real.sq_sqrt (hy0 _)] at hcs
          have h2ab : 0 ≤ 2 * α * β := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hcs h2ab]
      _ = (α * Real.sqrt (∑ c, x c) + β * Real.sqrt (∑ c, y c)) ^ 2 := by
          have hX : (Real.sqrt (∑ c, x c)) ^ 2 = ∑ c, x c :=
            Real.sq_sqrt (Finset.sum_nonneg fun c _ => hx0 c)
          have hY : (Real.sqrt (∑ c, y c)) ^ 2 = ∑ c, y c :=
            Real.sq_sqrt (Finset.sum_nonneg fun c _ => hy0 c)
          calc _ = α ^ 2 * (Real.sqrt (∑ c, x c)) ^ 2 +
                2 * α * β * (Real.sqrt (∑ c, x c) * Real.sqrt (∑ c, y c)) +
                β ^ 2 * (Real.sqrt (∑ c, y c)) ^ 2 := by rw [hX, hY]
            _ = _ := by ring
  refine ⟨summable_of_sum_le hn hfin, ?_⟩
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  exact Real.tsum_le_of_sum_le hn hfin

end

end ASDExplicitGamma.Main
