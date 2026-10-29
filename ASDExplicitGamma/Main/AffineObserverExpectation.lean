module

public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Native.OldSignedAffineFamilyAssembly
public import ASDExplicitGamma.Native.ParentBoundaryBandAffineCell
public import ASDExplicitGamma.Native.ParentBoundaryBandBlockLaw
public import ASDExplicitGamma.Native.ParentBoundaryBandMatrix
public import ASDExplicitGamma.Native.ParentBoundaryBandMatrixMean
public import ASDExplicitGamma.Inverse.ResponseCoefficients
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth
public import ASDExplicitGamma.Scalar.CellTranslation

/-! The affine family on an arbitrary observer root has the same source-cell
expectation as the origin `m-5` tile, by actual coefficient stationarity. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3

noncomputable section

private theorem main_affine_observer_scale'
    (m : ℤ) (hobs : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + (hobs : ℤ)))
      (hobs + 5)) : U.scale = m - 5 := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  dsimp only [originCube] at hs ⊢
  omega

private theorem main_affine_observer_block_translate'
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (U : TriadicCube 2)
    (plus : Bool) (ω : Cutoff.CutoffSample 2) :
    parentBoundaryBandNormalizedBlock M m 1 t U plus ω =
      parentBoundaryBandNormalizedBlock M m 1 t (originCube 2 U.scale) plus
        (Cutoff.translateCutoffSample (triadicCubeShift U) ω) := by
  unfold parentBoundaryBandNormalizedBlock
  rw [parent_boundary_band_coarse_cell_translate]

/-- The normalized diagonal block on any observer source cell has the same
integrable, isotropic expectation as the origin cell at scale `m-5`. -/
private theorem main_affine_observer_block_law'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (t : ℝ) (U : TriadicCube 2)
    (hscale : U.scale = m - 5) (plus : Bool) :
    (∀ i j, Integrable
      (fun ω => parentBoundaryBandNormalizedBlock M m 1 t U plus ω i j)
      (Cutoff.cutoffSampleLaw M).toMeasure) ∧
    (∀ i j, (∫ ω, parentBoundaryBandNormalizedBlock M m 1 t U plus ω i j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      if i = j then parentBoundaryBandBlockMean M m 1 t
        (originCube 2 (m - 5)) plus else 0) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let z := triadicCubeShift U
  let shift : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 :=
    fun ω => Cutoff.translateCutoffSample z ω
  have hU0scale : originCube 2 (m - 5) ∈
      descendantsAtScale (originCube 2 m) (m - 5) :=
    Algsuperdiff.Section3.Provider.ErrorComparison.originCube_mem_descendantsAtScale
      (d := 2) (by omega)
  have hU0depth : originCube 2 (m - 5) ∈ descendantsAtDepth (originCube 2 m)
      (Int.toNat ((originCube 2 m).scale - (m - 5))) := by
    rw [← descendantsAtScale_eq_descendantsAtDepth (originCube 2 m) (by
      simp only [originCube]
      omega)]
    exact hU0scale
  have hmp : MeasurePreserving shift μ μ := by
    exact ⟨Cutoff.measurable_translateCutoffSample z,
      Cutoff.map_translateCutoffSample_cutoffSampleLaw M z⟩
  have htranslate (ω : Cutoff.CutoffSample 2) (i j : Fin 2) :
      parentBoundaryBandNormalizedBlock M m 1 t U plus ω i j =
      parentBoundaryBandNormalizedBlock M m 1 t (originCube 2 (m - 5)) plus
        (shift ω) i j := by
    rw [main_affine_observer_block_translate']
    simp only [hscale, shift, z]
  have hbase := parent_boundary_band_block_scalar_law
    M h hM m 1 (by norm_num)
      (Int.toNat ((originCube 2 m).scale - (m - 5)))
      (originCube 2 (m - 5)) hU0depth t plus
  refine ⟨?_, ?_⟩
  · intro i j
    have hb := hbase.1 i j
    have hc : Integrable
        (fun ω => parentBoundaryBandNormalizedBlock M m 1 t
          (originCube 2 (m - 5)) plus (shift ω) i j) μ :=
      hmp.integrable_comp_of_integrable hb
    have hf : (fun ω => parentBoundaryBandNormalizedBlock M m 1 t U plus ω i j) =
        (fun ω => parentBoundaryBandNormalizedBlock M m 1 t
          (originCube 2 (m - 5)) plus (shift ω) i j) :=
      funext (fun ω => htranslate ω i j)
    rw [hf]
    exact hc
  · intro i j
    have hbaseMean := (parent_boundary_band_block_mean
      M h hM m 1 (by norm_num)
        (Int.toNat ((originCube 2 m).scale - (m - 5)))
        (originCube 2 (m - 5)) hU0depth t plus).2 i j
    calc
      (∫ ω, parentBoundaryBandNormalizedBlock M m 1 t U plus ω i j ∂μ) =
          ∫ ω, parentBoundaryBandNormalizedBlock M m 1 t (originCube 2 (m - 5)) plus
            (shift ω) i j ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun ω => htranslate ω i j)
      _ = ∫ ω, parentBoundaryBandNormalizedBlock M m 1 t
            (originCube 2 (m - 5)) plus ω i j ∂μ :=
        integral_cutoffSample_vadd M z
          (fun ω => parentBoundaryBandNormalizedBlock M m 1 t
            (originCube 2 (m - 5)) plus ω i j)
      _ = if i = j then parentBoundaryBandBlockMean M m 1 t
        (originCube 2 (m - 5)) plus else 0 := hbaseMean

private theorem main_affine_observer_band_eq_partial'
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω =
      (Model.partialInsertedCoefficient M m t ω).toFun := by
  funext x
  unfold attenuatedCoefficient Model.partialInsertedCoefficient
  have hioc : Finset.Ioc m (m + 1) = {m + 1} := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  rw [hioc]
  ext i j
  simp [Cutoff.coefficientCutoff_apply,
    Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]

private theorem main_affine_observer_mode_eq'
    (M : ABKModel 2) (Qroot : TriadicCube 2) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Qroot depth) (plus : Bool)
    (i : whiteBasisIndex) (col : Fin 2) (ω : Cutoff.CutoffSample 2) :
    let p := oldSignedBlockMean U (oldSignedFlatInput Qroot b L plus i col)
    let e := if plus then p.2 else p.1
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (oldSignedPartialFrameFieldAt M Qroot m t ω)) p) - blockVecDot p p =
    vecDot e (matVecMul
      (parentBoundaryBandNormalizedBlock M m 1 t U (!plus) ω) e) - vecNormSq e := by
  intro p e
  have hframe := old_signed_partial_cell_frame_at M Qroot m t ω U depth hU
  have hcoeff := main_affine_observer_band_eq_partial' M m t ω
  have hmatrix : coarseBlockMatrix (openCubeSet U)
      (oldSignedPartialFrameFieldAt M Qroot m t ω) =
      frameMatrix (Annealed.sigmaBar M m : ℝ)
        (coarseBlockMatrix (cubeSet U)
          (attenuatedCoefficient M m (m + 1) (fun _ => Real.sqrt t) ω)) := by
    calc
      _ = coarseBlockMatrix (cubeSet U)
          (oldSignedPartialFrameFieldAt M Qroot m t ω) :=
            (coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube U _).symm
      _ = frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet U)
            (Model.partialInsertedCoefficient M m t ω).toFun) := hframe
      _ = _ := by rw [hcoeff]
  rw [hmatrix]
  cases plus
  · have hp : p.2 = 0 := by
      apply funext
      intro k
      simp [p, oldSignedBlockMean, oldSignedFlatInput,
        oldSignedFlatMinusBlock, cubeAverage_const]
    simp [e, hp, parentBoundaryBandNormalizedBlock, frameMatrix,
      blockVecDot, blockMatVecMul, vecDot, vecNormSq, matVecMul,
      Fin.sum_univ_two]
  · have hp : p.1 = 0 := by
      apply funext
      intro k
      simp [p, oldSignedBlockMean, oldSignedFlatInput,
        oldSignedFlatPlusBlock, cubeAverage_const]
    simp [e, hp, parentBoundaryBandNormalizedBlock, frameMatrix,
      blockVecDot, blockMatVecMul, vecDot, vecNormSq, matVecMul,
      Fin.sum_univ_two]

/-- A complete signed affine column has its source scalar block coefficient
on any observer descendant cell. -/
private theorem main_affine_observer_column_integral'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Qroot : TriadicCube 2) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Qroot depth) (hscale : U.scale = m - 5)
    (plus : Bool) (col : Fin 2) :
    let p := fun i => oldSignedBlockMean U
      (oldSignedFlatInput Qroot b L plus i col)
    let f := fun ω => ∑' i,
      (blockVecDot (p i) (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
        (oldSignedPartialFrameFieldAt M Qroot m t ω)) (p i)) -
        blockVecDot (p i) (p i))
    Integrable f (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5))
        (!plus) - 1) * ∑' i, blockVecDot (p i) (p i) := by
  intro p f
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let A := parentBoundaryBandNormalizedBlock M m 1 t U (!plus)
  let c := parentBoundaryBandBlockMean M m 1 t
    (originCube 2 (m - 5)) (!plus)
  let E : whiteBasisIndex → Vec 2 := fun i =>
    if plus then (p i).2 else (p i).1
  have hlaw := main_affine_observer_block_law' M h hM m t U hscale (!plus)
  have hpos : ∀ ω e, 0 ≤ vecDot e (matVecMul (A ω) e) := by
    intro ω e
    exact parent_boundary_band_block_nonneg M m 1 t U (!plus) ω e
  have hnorm (i : whiteBasisIndex) : vecNormSq (E i) = blockVecDot (p i) (p i) := by
    cases plus <;> simp [E, p, oldSignedBlockMean, oldSignedFlatInput,
      oldSignedFlatPlusBlock, oldSignedFlatMinusBlock, cubeAverage_const,
      vecNormSq, vecDot, blockVecDot]
  have hs : Summable (fun i => vecNormSq (E i)) := by
    have hbase : Summable (fun i : whiteBasisIndex =>
        blockVecDot (oldSignedBlockMean U
          (oldSignedFlatInput Qroot b L plus i col))
          (oldSignedBlockMean U
            (oldSignedFlatInput Qroot b L plus i col))) := by
      cases plus
      · simpa only [oldSignedFlatInput, Bool.false_eq_true, ite_false] using
          old_signed_flat_minus_mean_series Qroot depth b L col U hU
      · simpa only [oldSignedFlatInput, ite_true] using
          old_signed_flat_plus_mean_series Qroot depth b L col U hU
    have hbase' : Summable (fun i => blockVecDot (p i) (p i)) :=
      hbase.congr (fun i => by
        dsimp only [p]
      )
    exact hbase'.congr (fun i => (hnorm i).symm)
  have hfamily := parent_boundary_signed_affine_family_integral μ A
    hlaw.1 hpos c hlaw.2 E hs
  have hf : f = (fun ω => ∑' i,
      (vecDot (E i) (matVecMul (A ω) (E i)) - vecNormSq (E i))) := by
    funext ω
    apply tsum_congr
    intro i
    exact main_affine_observer_mode_eq' M Qroot m t b L U depth hU
      plus i col ω
  rw [hf]
  have hsum : (∑' i, vecNormSq (E i)) = ∑' i, blockVecDot (p i) (p i) :=
    tsum_congr hnorm
  rw [hsum] at hfamily
  simpa [A, c, μ] using hfamily

/-- One complete signed affine source-cell family has the stationary scalar
expectation on the arbitrary observer partition. -/
private theorem main_affine_observer_cell_integral'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Qroot : TriadicCube 2) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Qroot depth) (hscale : U.scale = m - 5)
    (plus : Bool) :
    let f := fun ω => ∑' i, ∑ col : Fin 2,
      let p := oldSignedBlockMean U (oldSignedFlatInput Qroot b L plus i col)
      blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
        (oldSignedPartialFrameFieldAt M Qroot m t ω)) p) - blockVecDot p p
    Integrable f (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5))
        (!plus) - 1) * oldSignedFlatMeanSize Qroot U b L plus ^ 2 := by
  intro f
  let p := fun i col => oldSignedBlockMean U
    (oldSignedFlatInput Qroot b L plus i col)
  let q := fun col ω => ∑' i,
    (blockVecDot (p i col) (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (oldSignedPartialFrameFieldAt M Qroot m t ω)) (p i col)) -
      blockVecDot (p i col) (p i col))
  have hcol (col : Fin 2) := main_affine_observer_column_integral'
    M h hM Qroot m t b L U depth hU hscale plus col
  have hs (col : Fin 2) : Summable (fun i => blockVecDot (p i col) (p i col)) := by
    cases plus
    · exact old_signed_flat_minus_mean_series Qroot depth b L col U hU
    · exact old_signed_flat_plus_mean_series Qroot depth b L col U hU
  have he (ω : Cutoff.CutoffSample 2) : f ω = ∑ col : Fin 2, q col ω := by
    apply Summable.tsum_finsetSum
    intro col hcol'
    exact old_signed_affine_deviation_summable _ (fun i => p i col) (hs col)
  have hnorm : oldSignedFlatMeanSize Qroot U b L plus ^ 2 =
      ∑ col : Fin 2, ∑' i, blockVecDot (p i col) (p i col) := by
    unfold oldSignedFlatMeanSize
    change Real.sqrt (∑' i, ∑ col : Fin 2,
      blockVecDot (p i col) (p i col)) ^ 2 = _
    have hn : 0 ≤ ∑' i, ∑ col : Fin 2, blockVecDot (p i col) (p i col) :=
      tsum_nonneg (fun i => Finset.sum_nonneg (fun col _ =>
        add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)))
    rw [Real.sq_sqrt hn, Summable.tsum_finsetSum (fun col _ => hs col)]
  have hf : f = (fun ω => ∑ col : Fin 2, q col ω) := funext he
  rw [hf]
  refine ⟨integrable_finsetSum _ (fun col _ => (hcol col).1), ?_⟩
  rw [integral_finsetSum _ (fun col _ => (hcol col).1)]
  calc
    (∑ col : Fin 2, ∫ ω, q col ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∑ col : Fin 2, (parentBoundaryBandBlockMean M m 1 t
          (originCube 2 (m - 5)) (!plus) - 1) *
            ∑' i, blockVecDot (p i col) (p i col) := by
      apply Finset.sum_congr rfl
      intro col hcol'
      exact (hcol col).2
    _ =
        (parentBoundaryBandBlockMean M m 1 t
          (originCube 2 (m - 5)) (!plus) - 1) *
          ∑ col : Fin 2, ∑' i, blockVecDot (p i col) (p i col) := by
      rw [← Finset.mul_sum]
    _ = (parentBoundaryBandBlockMean M m 1 t
        (originCube 2 (m - 5)) (!plus) - 1) * oldSignedFlatMeanSize Qroot U b L plus ^ 2 := by
      exact congrArg (fun x : ℝ =>
        (parentBoundaryBandBlockMean M m 1 t
          (originCube 2 (m - 5)) (!plus) - 1) * x) hnorm.symm

private theorem main_affine_observer_family_integral'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Qroot : TriadicCube 2) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (depth : ℕ)
    (hscale : ∀ U, U ∈ descendantsAtDepth Qroot depth → U.scale = m - 5)
    (plus : Bool) :
    let family := fun ω => ∑' n,
      descendantsAverage Qroot depth (fun U => ∑ i : Fin 2,
        (let p := oldSignedBlockMean U
          (oldSignedFlatInput Qroot b L plus n i)
         blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
           (oldSignedPartialFrameFieldAt M Qroot m t ω)) p) -
           blockVecDot p p))
    Integrable family (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, family ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5))
        (!plus) - 1) * descendantsAverage Qroot depth
          (fun U => oldSignedFlatMeanSize Qroot U b L plus ^ 2) := by
  intro family
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun U ω => ∑' i, ∑ col : Fin 2,
    let p := oldSignedBlockMean U (oldSignedFlatInput Qroot b L plus i col)
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U)
      (oldSignedPartialFrameFieldAt M Qroot m t ω)) p) - blockVecDot p p
  have hcell (U : TriadicCube 2)
      (hU : U ∈ descendantsAtDepth Qroot depth) :=
    main_affine_observer_cell_integral' M h hM Qroot m t b L U depth hU
      (hscale U hU) plus
  have he (ω : Cutoff.CutoffSample 2) : family ω =
      descendantsAverage Qroot depth (fun U => f U ω) :=
    (old_signed_partition_series Qroot depth _
      (old_signed_flat_affine_family_cell_summable Qroot depth
        (oldSignedPartialFrameFieldAt M Qroot m t ω) b L plus)).2
  have hfun : family = (fun ω => descendantsAverage Qroot depth (fun U => f U ω)) :=
    funext he
  rw [hfun]
  refine ⟨?_, ?_⟩
  · unfold descendantsAverage
    exact (integrable_finsetSum _ (fun U hU => (hcell U hU).1)).const_mul _
  · rw [old_signed_integral_descendants_average _ Qroot depth f
      (fun U hU => (hcell U hU).1)]
    dsimp only [descendantsAverage]
    calc
      _ = ((descendantsAtDepth Qroot depth).card : ℝ)⁻¹ *
          ∑ U ∈ descendantsAtDepth Qroot depth,
          (parentBoundaryBandBlockMean M m 1 t
            (originCube 2 (m - 5)) (!plus) - 1) *
              oldSignedFlatMeanSize Qroot U b L plus ^ 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro U hU
        simpa only [f] using (hcell U hU).2
      _ = _ := by
        rw [← Finset.mul_sum]
        ring

/-- Exact expectation of the observer-rooted signed affine contribution,
expressed through its two OLD-frame scalar means and flat mean sizes. -/
theorem main_affine_observer_affine_identity
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hobs : ℕ) (t b : ℝ) (L : {l : ℝ // 0 < l}) :
    let Qroot := originCube 2 (m + (hobs : ℤ))
    let depth := hobs + 5
    let q := parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5)) false - 1
    let p := parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5)) true - 1
    let X := descendantsAverage Qroot depth
      (fun U => oldSignedFlatMeanSize Qroot U b L true ^ 2)
    let Y := descendantsAverage Qroot depth
      (fun U => oldSignedFlatMeanSize Qroot U b L false ^ 2)
    (∫ ω, oldSignedFlatAffineContribution Qroot depth
      (oldSignedPartialFrameFieldAt M Qroot m t ω) b L
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = q * X + p * Y := by
  dsimp only
  let Qroot : TriadicCube 2 := originCube 2 (m + (hobs : ℤ))
  let depth := hobs + 5
  let a := fun ω => oldSignedPartialFrameFieldAt M Qroot m t ω
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let q := parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5)) false - 1
  let p := parentBoundaryBandBlockMean M m 1 t (originCube 2 (m - 5)) true - 1
  let X := descendantsAverage Qroot depth
    (fun U => oldSignedFlatMeanSize Qroot U b L true ^ 2)
  let Y := descendantsAverage Qroot depth
    (fun U => oldSignedFlatMeanSize Qroot U b L false ^ 2)
  let family := fun plus ω => ∑' n,
    descendantsAverage Qroot depth (fun U => ∑ i : Fin 2,
      (let v := oldSignedBlockMean U (oldSignedFlatInput Qroot b L plus n i)
       blockVecDot v (blockMatVecMul (coarseBlockMatrix (openCubeSet U) (a ω)) v) -
         blockVecDot v v))
  have hscale : ∀ U, U ∈ descendantsAtDepth Qroot depth → U.scale = m - 5 := by
    intro U hU
    exact main_affine_observer_scale' m hobs U (by simpa [Qroot, depth] using hU)
  have hplus := main_affine_observer_family_integral' M h hM Qroot m t b L
    depth hscale true
  have hminus := main_affine_observer_family_integral' M h hM Qroot m t b L
    depth hscale false
  have hsum (ω : Cutoff.CutoffSample 2) :=
    old_signed_flat_affine_family_sum Qroot depth (a ω) b L
  have hpoint (ω : Cutoff.CutoffSample 2) :
      oldSignedFlatAffineContribution Qroot depth (a ω) b L =
        family true ω + family false ω := by
    exact (hsum ω).symm
  calc
    _ = ∫ ω, family true ω + family false ω ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (∫ ω, family true ω ∂μ) + ∫ ω, family false ω ∂μ :=
      integral_add hplus.1 hminus.1
    _ = q * X + p * Y := by
      rw [hplus.2, hminus.2]
      rfl

end
end ASDExplicitGamma.Main

end
