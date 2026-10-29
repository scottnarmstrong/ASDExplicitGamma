module

public import ASDExplicitGamma.Main.HotPatchRow
public import ASDExplicitGamma.Main.Q3ResidualHilbertSchmidt
public import ASDExplicitGamma.Native.OldSignedSourceMultiplier
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! Hot-patch trial, package C: the source-size bound
`d' ≤ k_a K(∇w) + k_d K(∇φ)` for the actual hot-patched source, for every finite
family of fresh modes and each canonical load. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Native

local instance hotBoundFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem main_descendantsAverage_finset_sum_univ {ι : Type*} [Fintype ι] (Q : TriadicCube 2)
    (j : ℕ) (f : ι → TriadicCube 2 → ℝ) :
    ∑ c : ι, descendantsAverage Q j (f c) =
      descendantsAverage Q j (fun U => ∑ c : ι, f c U) :=
  (main_descendantsAverage_finset_sum Q j Finset.univ f).symm

/-- Weak Haar energy depends only on the field on the open cell. -/
theorem hot_vectorWeakHaarEnergy_congr_open (U : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure U))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure U))
    (h : ∀ x ∈ openCubeSet U, F x = G x) :
    vectorWeakHaarEnergy U F = vectorWeakHaarEnergy U G := by
  have hq : 1 < Real.sqrt 3 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
    simpa using h
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply lemmaV_dualEnergy_congr_ae U hq (hF i) (hG i)
  have h1 : ∀ᵐ x ∂(volume.restrict (openCubeSet U)), F x i = G x i :=
    (ae_restrict_iff' (measurableSet_openCubeSet U)).2
      (Filter.Eventually.of_forall fun x hx => congrFun (h x hx) i)
  rw [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet U)]
  exact h1

/-- On a cell, the weak energy of the glued corrector's gradient is that of the cell
corrector's gradient. -/
theorem hot_corrector_cell_weak_energy_eq (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    vectorWeakHaarEnergy U (fun x i => (oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)).toH1Function.grad x i) =
    vectorWeakHaarEnergy U (fun x i =>
      (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function.grad x i) := by
  apply hot_vectorWeakHaarEnergy_congr_open U
  · intro i
    exact (oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)).toH1Function.grad_memL2_normalizedCubeMeasure i
  · intro i
    exact memLp_on_descendant_of_memLp hU
      ((hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function.grad_memL2_normalizedCubeMeasure i)
  · intro x hx
    funext i
    rw [hot_glued_corrector_grad_cell Q depth nu sigma hnu hsigma k P U hU x hx]

/-- The hot-patched source obeys, for every finite family `s` of fresh modes and each
constant load `P`, the size bound `d' ≤ k_a K(∇w) + k_d K(∇φ)` in the tile-averaged
positive Haar energy, with the `w`-row paid by the DIAG source multiplier and the
local corrector paid by the derivative-column constant. -/
theorem hot_source_load_energy_finset (m : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 m) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (P : BlockVec 2) (s : Finset whiteBasisIndex) :
    let Q := originCube 2 m
    Real.sqrt (∑ l ∈ s, descendantsAverage Q depth (fun U => vectorPositiveHaarEnergy U
      (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2))) ≤
      oldSignedSourceMultiplier Q depth b L *
          Real.sqrt (lemmaVTiledWeakEnergy Q depth
            (hotPatchPotential Q depth nu sigma hnu hsigma k P).toH1Function.grad) +
        mainKd (b ^ 2) * Real.sqrt (lemmaVTiledWeakEnergy Q depth
          (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function.grad) := by
  intro Q
  classical
  let w := hotPatchPotential Q depth nu sigma hnu hsigma k P
  let φ := hotGluedCorrector Q depth nu sigma hnu hsigma k P
  let E : TriadicCube 2 → ℝ := fun U => ∑ l ∈ s, vectorPositiveHaarEnergy U
    (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2)
  let F1 : TriadicCube 2 → ℝ := fun U => ∑ l ∈ s, vectorPositiveHaarEnergy U
    (lemmaVPlanarRowField (diagInterpolant Q depth)
      (pureFluxMainQ3BasisFrameMultiplier m b 1 L l)
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 w))
  let K : TriadicCube 2 → ℝ := fun U => vectorWeakHaarEnergy U
    (fun x i => φ.toH1Function.grad x i)
  have hkd : 0 ≤ mainKd (b ^ 2) := mainKd_nonneg (b ^ 2)
  have hE0 (U : TriadicCube 2) (_ : U ∈ descendantsAtDepth Q depth) : 0 ≤ E U :=
    Finset.sum_nonneg fun l _ => vectorPositiveHaarEnergy_nonneg U _
  have hF0 (U : TriadicCube 2) (_ : U ∈ descendantsAtDepth Q depth) : 0 ≤ F1 U :=
    Finset.sum_nonneg fun l _ => vectorPositiveHaarEnergy_nonneg U _
  have hK0 (U : TriadicCube 2) (_ : U ∈ descendantsAtDepth Q depth) : 0 ≤ K U :=
    vectorWeakHaarEnergy_nonneg U _
  have hb (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      Real.sqrt (E U) ≤ 1 * Real.sqrt (F1 U) + mainKd (b ^ 2) * Real.sqrt (K U) +
        0 * Real.sqrt (K U) := by
    let φU := oldSignedCellFirstCorrector Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
    have hE := hot_source_tile_energy_eq Q depth nu sigma hnu hsigma k b L P s U hU
    have htri := (hot_row_tile_triangle Q depth w s U hU b L φU).2.2
    have hrowEq := pureFluxMainQ3FiniteRawRow_tile_energy_eq_hotcopy m b L depth 0 w s U hU
    dsimp only at hrowEq
    rw [ASDExplicitGamma.Native.old_signed_zero_affine_potential] at hrowEq
    have hcol := hot_row_corrector_energy_le s b L U φU
    have hkdU : mainQ3ColumnConstant (cubeScaleFactor U) b L.1 ≤ mainKd (b ^ 2) :=
      mainQ3ColumnConstant_le_mainKd (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' U) (hL U hU)
    have hKeq := hot_corrector_cell_weak_energy_eq Q depth nu sigma hnu hsigma k P U hU
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
    have hC1 : hilbertPrimalEnergy U (Real.sqrt 3)
        (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q depth w.toH1Function) = F1 U := by
      simp only [F1]
      rw [ASDExplicitGamma.Native.old_signed_zero_affine_potential]
      exact hrowEq.symm
    simp only [one_mul, zero_mul, add_zero]
    rw [show E U = _ from hE]
    refine htri.trans ?_
    rw [hC1]
    exact add_le_add le_rfl hC2
  have hagg := sqrt_descendantsAverage_energy_bound_three Q depth E F1 K K
    (A := 1) (B := mainKd (b ^ 2)) (C := 0) (by norm_num) hkd le_rfl hE0 hF0 hK0 hK0 hb
  have hAvgE : descendantsAverage Q depth E = ∑ l ∈ s, descendantsAverage Q depth (fun U =>
      vectorPositiveHaarEnergy U
        (fun x => (hotPatchSource Q depth depth nu sigma hnu hsigma k b L l P x).2)) :=
    main_descendantsAverage_finset_sum Q depth s _
  have hAvgF : descendantsAverage Q depth F1 =
      ∑ l ∈ s, pureFluxMainQ3RowEnergy m b 1 L depth 0 w l := by
    rw [show F1 = fun U => ∑ l ∈ s, vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant Q depth)
        (pureFluxMainQ3BasisFrameMultiplier m b 1 L l)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 w)) from rfl]
    rw [main_descendantsAverage_finset_sum Q depth s _]
    rfl
  have hrow := pureFluxMainQ3Row_trace_finset_sharp m b L depth 0 w s
  dsimp only at hrow
  rw [ASDExplicitGamma.Native.old_signed_zero_affine_potential] at hrow
  rw [← hAvgF] at hrow
  rw [← hAvgE]
  have hK : descendantsAverage Q depth K = lemmaVTiledWeakEnergy Q depth
      (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function.grad := rfl
  rw [hK] at hagg
  have hmult : oldSignedSourceMultiplier Q depth b L = Real.sqrt (b ^ 2) +
      diagMeshRadius Q depth * (36 / 25) * Real.sqrt ((156 / 5) * b ^ 2 / L.1 ^ 2) +
        (diagMeshRadius Q depth) ^ 2 * (57 / 200) *
          Real.sqrt ((46488 / 25) * b ^ 2 / L.1 ^ 4) := rfl
  calc Real.sqrt (descendantsAverage Q depth E) ≤ _ := hagg
    _ ≤ _ := by
      simp only [one_mul, zero_mul, add_zero]
      rw [hmult]
      exact add_le_add hrow le_rfl

/-- Package C. For the four canonical loads and the complete family of fresh modes, the
hot-patched source `f'` has summable tile-averaged positive energy and its size
`d' = (Σ_{n,c} avg_U P_U(f'_{n,c})²)^{1/2}` obeys
`d' ≤ k_a K(∇w) + k_d K(∇φ)`, with `K` the four-load tiled weak norms. -/
theorem hot_source_size_bound (m : ℤ) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth (originCube 2 m) depth, cubeScaleFactor R * 3 ^ 6 ≤ L.1) :
    let Q := originCube 2 m
    let src : whiteBasisIndex → ℝ := fun n => ∑ c : BlockCoord 2,
      descendantsAverage Q depth (fun U => vectorPositiveHaarEnergy U (fun x =>
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2))
    Summable src ∧
    Real.sqrt (∑' n, src n) ≤
      oldSignedSourceMultiplier Q depth b L *
          Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q depth
            (hotPatchPotential Q depth nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) +
        mainKd (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q depth
          (hotGluedCorrector Q depth nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) := by
  intro Q src
  classical
  let α := oldSignedSourceMultiplier Q depth b L
  let β := mainKd (b ^ 2)
  let x : BlockCoord 2 → ℝ := fun c => lemmaVTiledWeakEnergy Q depth
    (hotPatchPotential Q depth nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad
  let y : BlockCoord 2 → ℝ := fun c => lemmaVTiledWeakEnergy Q depth
    (hotGluedCorrector Q depth nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad
  let srcc : whiteBasisIndex → BlockCoord 2 → ℝ := fun n c =>
    descendantsAverage Q depth (fun U => vectorPositiveHaarEnergy U (fun x =>
      (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (blockBasis c) x).2))
  have hα : 0 ≤ α := by
    have hr := diagMeshRadius_pos Q depth
    unfold α oldSignedSourceMultiplier
    positivity
  have hβ : 0 ≤ β := mainKd_nonneg (b ^ 2)
  have hx0 (c : BlockCoord 2) : 0 ≤ x c :=
    descendantsAverage_nonneg Q depth _ (fun U _ => vectorWeakHaarEnergy_nonneg U _)
  have hy0 (c : BlockCoord 2) : 0 ≤ y c :=
    descendantsAverage_nonneg Q depth _ (fun U _ => vectorWeakHaarEnergy_nonneg U _)
  have hs0 (n : whiteBasisIndex) (c : BlockCoord 2) : 0 ≤ srcc n c :=
    descendantsAverage_nonneg Q depth _ (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hn (n : whiteBasisIndex) : 0 ≤ src n :=
    Finset.sum_nonneg fun c _ => hs0 n c
  have hfin (s : Finset whiteBasisIndex) :
      ∑ n ∈ s, src n ≤ (α * Real.sqrt (∑ c, x c) + β * Real.sqrt (∑ c, y c)) ^ 2 := by
    have hload (c : BlockCoord 2) : ∑ n ∈ s, srcc n c ≤
        α ^ 2 * x c + 2 * α * β * (Real.sqrt (x c) * Real.sqrt (y c)) + β ^ 2 * y c := by
      have h := hot_source_load_energy_finset m depth nu sigma hnu hsigma k b L hL
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

end ASDExplicitGamma.Inverse
