module

public import ASDExplicitGamma.Main.HotCovCellBound

/-! MA-E-COVARIANCE, step 14: the exact cell-level mode series of the affine carrier.
For one source cell, one load and one sign, the mode series of the carrier equals
`2 P̄ - v <J z, rcv(J e_i)> - 2 <J z, rcv(ε_i)>` with `ε_i` the boundary-error column
of the cell covariance matrix and `P̄` the (K/P bounded) residual-source series. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- The pairing of the frozen direction `J z` with a receiver, on a cell. -/
abbrev hotCovEll (Q : TriadicCube 2) (d : ℕ) (U : OldSignedCellIndex Q d)
    (w : H10Function (openCubeSet Q)) (e : Vec 2 → Vec 2) : ℝ :=
  hotCovCross U.val (hotCovZfield Q d w) e

/-- Column `i` of the identity rotation: `J e_i`. -/
def hotCovJcol (i : Fin 2) : Vec 2 := fun a => responsePlanarJ a i

/-- Column `i` of the cell covariance boundary error. -/
def hotCovErrCol (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool)
    (i : Fin 2) : Vec 2 := fun a => hotCovMeanCovErr Q U b L plus a i

/-- The residual-source/receiver cross series on one cell. -/
def hotCovResSeries (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (U : OldSignedCellIndex Q d) (P : BlockVec 2) (plus : Bool) (i : Fin 2)
    (rcv : Vec 2 → Vec 2 → Vec 2) : ℝ :=
  ∑' n : whiteBasisIndex, volumeAverage (openCubeSet U.val) (fun x =>
    vecDot (hotCovRem Q d nu sigma hnu hsigma k b L n P U.val x)
      (rcv (hotCovFlatMeanVec Q b L plus U.val n i) x))

theorem hotCov_cell_series_generic (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1)
    (U : OldSignedCellIndex Q d) (c : BlockCoord 2) (plus : Bool) (i : Fin 2)
    (rcv : Vec 2 → Vec 2 → Vec 2)
    (hrcv : ∀ ν, MemVectorL2 (openCubeSet U.val) (rcv ν))
    (hlin : ∀ ν, ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      rcv ν x = ν 0 • rcv (basisVec 0) x + ν 1 • rcv (basisVec 1) x)
    (hKsum : Summable (fun n : whiteBasisIndex => vectorWeakHaarEnergy U.val
      (rcv (hotCovFlatMeanVec Q b L plus U.val n i)))) :
    |hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) plus i rcv| ≤
        Real.sqrt (∑' n : whiteBasisIndex, vectorPositiveHaarEnergy U.val
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x)) *
        Real.sqrt (∑' n : whiteBasisIndex, vectorWeakHaarEnergy U.val
          (rcv (hotCovFlatMeanVec Q b L plus U.val n i))) ∧
      HasSum (fun n : whiteBasisIndex => mainECellCrossCarrier U.val
          (fun x => -(hotPatchSource Q d d nu sigma hnu hsigma k b L n (blockBasis c) x).2)
          (rcv (hotCovFlatMeanVec Q b L plus U.val n i)))
        (2 * hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) plus i rcv -
          b ^ 2 * hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
            (rcv (hotCovJcol i)) -
          2 * hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
            (rcv (hotCovErrCol Q U.val b L plus i))) := by
  classical
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let w := hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)
  let X : Vec 2 → Vec 2 := fun x => planarQuarterTurn (hotCovZfield Q d w x)
  let A : whiteBasisIndex → ℝ := fun n => cubeAverage U.val (hotCovPsi b L n)
  let μ : whiteBasisIndex → Vec 2 := fun n => hotCovFlatMeanVec Q b L plus U.val n i
  let g : whiteBasisIndex → Vec 2 → Vec 2 := fun n x =>
    (hotPatchSource Q d d nu sigma hnu hsigma k b L n (blockBasis c) x).2
  let rem : whiteBasisIndex → Vec 2 → Vec 2 := fun n =>
    hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val
  have hrem : ∀ n x, rem n x = g n x + A n • X x := fun n x => rfl
  have hg : ∀ n, MemVectorL2 (openCubeSet U.val) (g n) := fun n =>
    hotCov_source_memL2 Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val hsub
  have hX : MemVectorL2 (openCubeSet U.val) X :=
    hotCov_memVectorL2_quarterTurn
      ((hotCov_zfield_memL2 Q d w).mono_measure (Measure.restrict_mono_set volume hsub))
  -- the covariance series
  let Nmat := hotCovMeanCov Q U.val b L plus
  have hM : ∀ a, HasSum (fun n => A n * μ n a) (Nmat a i) := fun a =>
    hotCov_meanCov_entry Q d b L plus U.val U.property i a
  have hN : ∀ a, Nmat a i = (b ^ 2 / 2) * responsePlanarJ a i +
      hotCovMeanCovErr Q U.val b L plus a i := by
    intro a
    simp [hotCovMeanCovErr, Nmat]
  -- the residual series
  let a' : whiteBasisIndex → ℝ := fun n => vectorPositiveHaarNorm U.val (rem n)
  let b' : whiteBasisIndex → ℝ := fun n => vectorWeakHaarNorm U.val (rcv (μ n))
  have ha2 : Summable (fun n => a' n ^ 2) := by
    have := hotCov_rem_sq_summable Q d nu sigma hnu hsigma k b L hL hmesh U.val U.property c
    refine this.congr (fun n => ?_)
    simp only [a', vectorPositiveHaarNorm, Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
    rfl
  have hb2 : Summable (fun n => b' n ^ 2) := by
    refine hKsum.congr (fun n => ?_)
    simp only [b', vectorWeakHaarNorm, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
    rfl
  have hbudget := old_signed_series_pairing_budget (I := whiteBasisIndex)
    b' a' (fun n => volumeAverage (openCubeSet U.val)
      (fun x => vecDot (rem n x) (rcv (μ n) x)))
    (fun n => Real.sqrt_nonneg _) (fun n => Real.sqrt_nonneg _) hb2 ha2
    (fun n => hotCov_rem_pair_bound Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val
      U.property _ (hrcv _))
  obtain ⟨hPs, hPb⟩ := hbudget
  refine ⟨?_, ?_⟩
  · refine hPb.trans (le_of_eq ?_)
    have e1 : (∑' n, b' n ^ 2) = ∑' n : whiteBasisIndex,
        vectorWeakHaarEnergy U.val (rcv (hotCovFlatMeanVec Q b L plus U.val n i)) := by
      refine tsum_congr (fun n => ?_)
      simp only [b', vectorWeakHaarNorm, μ, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
    have e2 : (∑' n, a' n ^ 2) = ∑' n : whiteBasisIndex, vectorPositiveHaarEnergy U.val
        (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x) := by
      refine tsum_congr (fun n => ?_)
      simp only [a', vectorPositiveHaarNorm, rem, Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
    rw [e1, e2]
    ring
  · have hser := hotCov_cell_mode_hasSum U.val X rem g A μ rcv hrem hg hX hrcv hlin
      (fun a => Nmat a i) hM _ hPs.hasSum
    have hMeq : volumeAverage (openCubeSet U.val) (fun x => vecDot (X x) (rcv (fun a => Nmat a i) x)) =
        (b ^ 2 / 2) * volumeAverage (openCubeSet U.val)
          (fun x => vecDot (X x) (rcv (hotCovJcol i) x)) +
        volumeAverage (openCubeSet U.val)
          (fun x => vecDot (X x) (rcv (hotCovErrCol Q U.val b L plus i) x)) := by
      rw [hotCov_ell_linear U.val X rcv hX hrcv hlin (fun a => Nmat a i),
        hotCov_ell_linear U.val X rcv hX hrcv hlin (hotCovJcol i),
        hotCov_ell_linear U.val X rcv hX hrcv hlin (hotCovErrCol Q U.val b L plus i)]
      simp only [hN, hotCovJcol, hotCovErrCol]
      ring
    rw [hMeq] at hser
    convert hser using 1
    unfold hotCovResSeries hotCovEll hotCovCross
    ring

end

end ASDExplicitGamma.Main
