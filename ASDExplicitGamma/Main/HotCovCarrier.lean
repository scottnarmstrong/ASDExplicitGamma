module

public import ASDExplicitGamma.Main.HotCovRem
public import ASDExplicitGamma.Main.HotCovLinear
public import ASDExplicitGamma.Main.HotCovFlatMean
public import ASDExplicitGamma.Main.HotCovFlatError
public import ASDExplicitGamma.Main.ETermMixedCarrier
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Scalar.CoefficientFlux

/-! MA-E-COVARIANCE, step 11: the affine C carrier of the hot trial and its exact
mode-sum reduction.  The carrier is the non-flat source cross `-2 <f', e_aff>` with the
affine reciprocal receiver `e_aff` (the local canonical minimizer for the cell-mean
datum).  Summed over the Gaussian modes it becomes
`2 Σ_n <rem_n, e_n> - 2 <J z, rcv(M)>` with `M = Σ_n a_n m_n = N_U e_i`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- The cell-mean datum `m^±_{n,i,U}` of the finite-parent flat coordinates. -/
abbrev hotCovFlatMeanVec (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool)
    (U : TriadicCube 2) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 :=
  fun l => hotCovFlatMean Q b L plus U n i l

/-- Affine top contribution of the hot trial on one cell, for one mode and load. -/
def hotCovTopAffCross (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) (U : OldSignedCellIndex Q d) : ℝ :=
  mainECellCrossCarrier U.val
    (fun x => -(hotPatchSource Q d d nu sigma hnu hsigma k b L n (oldSignedFlatLoad true i) x).2)
    (hotCovTopRcv Q d nu sigma hnu hsigma k U (hotCovFlatMeanVec Q b L true U.val n i))

/-- Affine bottom contribution of the hot trial on one cell. -/
def hotCovBotAffCross (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) (U : OldSignedCellIndex Q d) : ℝ :=
  mainECellCrossCarrier U.val
    (fun x => -(hotPatchSource Q d d nu sigma hnu hsigma k b L n (oldSignedFlatLoad false i) x).2)
    (hotCovBotRcv Q d nu sigma hnu hsigma k U (hotCovFlatMeanVec Q b L false U.val n i))

/-- Modewise affine covariance carrier of the hot trial, over the actual top and bottom
loads. -/
def hotCovAffMode (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (U : OldSignedCellIndex Q d) : ℝ :=
  (∑ i : Fin 2, hotCovTopAffCross Q d nu sigma hnu hsigma k b L n i U) +
    ∑ i : Fin 2, hotCovBotAffCross Q d nu sigma hnu hsigma k b L n i U

/-- The affine C carrier: the complete mode series of the equal-volume cell average. -/
def hotCovAffCarrier (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  ∑' n : whiteBasisIndex, oldSignedCellAverage Q d
    (hotCovAffMode Q d nu sigma hnu hsigma k b L n)

/-- Source-row identity of the carrier through `mainECellTopAffineOfFlatInput`: the
cell-mean datum is the actual source datum `-(mean of the native top input).2`. -/
theorem hotCovTopAffCross_eq (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) (U : OldSignedCellIndex Q d) :
    hotCovTopAffCross Q d nu sigma hnu hsigma k b L n i U =
      mainECellCrossCarrier U.val
        (fun x => -(hotPatchSource Q d d nu sigma hnu hsigma k b L n
          (oldSignedFlatLoad true i) x).2)
        (mainECellTopAffineOfFlatInput U.val
          (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
          (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
            nu sigma hnu hsigma (hotCovCellCoef Q d k U))
          (oldSignedFlatInput Q b L true n i)) := by
  unfold hotCovTopAffCross
  congr 1
  have h : -(oldSignedBlockMean U.val (oldSignedFlatInput Q b L true n i)).2 =
      hotCovFlatMeanVec Q b L true U.val n i := by
    funext l
    have := hotCov_block_mean_coordinate Q b L true U.val n i l
    simp only [if_true] at this
    simp [this]
  change hotCovTopRcv Q d nu sigma hnu hsigma k U _ =
    hotCovTopRcv Q d nu sigma hnu hsigma k U _
  rw [h]

theorem hotCovBotAffCross_eq (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) (U : OldSignedCellIndex Q d) :
    hotCovBotAffCross Q d nu sigma hnu hsigma k b L n i U =
      mainECellCrossCarrier U.val
        (fun x => -(hotPatchSource Q d d nu sigma hnu hsigma k b L n
          (oldSignedFlatLoad false i) x).2)
        (mainECellBottomAffineOfFlatInput U.val
          (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U))
          (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
            nu sigma hnu hsigma (hotCovCellCoef Q d k U))
          (oldSignedFlatInput Q b L false n i)) := by
  unfold hotCovBotAffCross
  congr 1

/-- Pointwise: `<-g, e> = -<rem, e> + A <J z, e>` when `rem = g + A J z`. -/
theorem hotCov_cross_decomp (U : TriadicCube 2) (g rem X e : Vec 2 → Vec 2) (A : ℝ)
    (hrem : ∀ x, rem x = g x + A • X x) (hg : MemVectorL2 (openCubeSet U) g)
    (hX : MemVectorL2 (openCubeSet U) X) (he : MemVectorL2 (openCubeSet U) e) :
    mainECellCrossCarrier U (fun x => -g x) e =
      2 * volumeAverage (openCubeSet U) (fun x => vecDot (rem x) (e x)) -
        2 * A * volumeAverage (openCubeSet U) (fun x => vecDot (X x) (e x)) := by
  have hgi := integrableOn_vecDot_of_memVectorL2 hg he
  have hXi := integrableOn_vecDot_of_memVectorL2 hX he
  have h1 : (fun x => vecDot (-g x) (e x)) =
      fun x => -(vecDot (g x) (e x)) := by
    funext x; simp [vecDot, Finset.sum_neg_distrib]
  have h2 : (fun x => vecDot (rem x) (e x)) =
      fun x => vecDot (g x) (e x) + A * vecDot (X x) (e x) := by
    funext x
    simp only [hrem x, vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold mainECellCrossCarrier
  rw [h1, h2]
  have hA : IntegrableOn (fun x => A * vecDot (X x) (e x)) (openCubeSet U) volume :=
    hXi.const_mul A
  unfold volumeAverage
  rw [integral_neg, integral_add hgi hA, integral_const_mul]
  ring

/-- The pairing with a linear (a.e.) receiver family is linear in the datum. -/
theorem hotCov_ell_linear (U : TriadicCube 2) (X : Vec 2 → Vec 2)
    (rcv : Vec 2 → Vec 2 → Vec 2)
    (hX : MemVectorL2 (openCubeSet U) X) (hrcv : ∀ ν, MemVectorL2 (openCubeSet U) (rcv ν))
    (hlin : ∀ ν, ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U)),
      rcv ν x = ν 0 • rcv (basisVec 0) x + ν 1 • rcv (basisVec 1) x) (ν : Vec 2) :
    volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv ν x)) =
      ν 0 * volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv (basisVec 0) x)) +
        ν 1 * volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv (basisVec 1) x)) := by
  have hi0 := integrableOn_vecDot_of_memVectorL2 hX (hrcv (basisVec 0))
  have hi1 := integrableOn_vecDot_of_memVectorL2 hX (hrcv (basisVec 1))
  have hae : (fun x => vecDot (X x) (rcv ν x)) =ᵐ[volume.restrict (openCubeSet U)]
      (fun x => ν 0 * vecDot (X x) (rcv (basisVec 0) x) +
        ν 1 * vecDot (X x) (rcv (basisVec 1) x)) := by
    filter_upwards [hlin ν] with x hx
    rw [hx]
    simp [vecDot, Finset.sum_add_distrib, Finset.mul_sum, Fin.sum_univ_two]
    ring
  unfold volumeAverage
  rw [integral_congr_ae hae, integral_add (hi0.const_mul _) (hi1.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- Mode-sum reduction on one cell: with `g_n = rem_n - A_n X`, the carriers
`-2<g_n, e_n>` (`e_n = rcv(μ_n)` linear in the datum) sum to
`2 Σ_n <rem_n, e_n> - 2 <X, rcv(M)>`, `M = Σ_n A_n μ_n`. -/
theorem hotCov_cell_mode_hasSum (U : TriadicCube 2) {ι : Type*}
    (X : Vec 2 → Vec 2) (rem g : ι → Vec 2 → Vec 2) (A : ι → ℝ) (μ : ι → Vec 2)
    (rcv : Vec 2 → Vec 2 → Vec 2)
    (hrem : ∀ n x, rem n x = g n x + A n • X x)
    (hg : ∀ n, MemVectorL2 (openCubeSet U) (g n))
    (hX : MemVectorL2 (openCubeSet U) X) (hrcv : ∀ ν, MemVectorL2 (openCubeSet U) (rcv ν))
    (hlin : ∀ ν, ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U)),
      rcv ν x = ν 0 • rcv (basisVec 0) x + ν 1 • rcv (basisVec 1) x)
    (M : Vec 2) (hM : ∀ a, HasSum (fun n => A n * μ n a) (M a))
    (P : ℝ) (hP : HasSum (fun n => volumeAverage (openCubeSet U)
      (fun x => vecDot (rem n x) (rcv (μ n) x))) P) :
    HasSum (fun n => mainECellCrossCarrier U (fun x => -g n x) (rcv (μ n)))
      (2 * P - 2 * volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv M x))) := by
  have hell : ∀ ν : Vec 2, volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv ν x)) =
      ν 0 * volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv (basisVec 0) x)) +
        ν 1 * volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv (basisVec 1) x)) := by
    intro ν
    have hi0 := integrableOn_vecDot_of_memVectorL2 hX (hrcv (basisVec 0))
    have hi1 := integrableOn_vecDot_of_memVectorL2 hX (hrcv (basisVec 1))
    have hae : (fun x => vecDot (X x) (rcv ν x)) =ᵐ[volume.restrict (openCubeSet U)]
        (fun x => ν 0 * vecDot (X x) (rcv (basisVec 0) x) +
          ν 1 * vecDot (X x) (rcv (basisVec 1) x)) := by
      filter_upwards [hlin ν] with x hx
      rw [hx]
      simp [vecDot, Finset.sum_add_distrib, Finset.mul_sum, Fin.sum_univ_two]
      ring
    unfold volumeAverage
    rw [integral_congr_ae hae, integral_add (hi0.const_mul _) (hi1.const_mul _),
      integral_const_mul, integral_const_mul]
    ring
  set l0 := volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv (basisVec 0) x)) with hl0
  set l1 := volumeAverage (openCubeSet U) (fun x => vecDot (X x) (rcv (basisVec 1) x)) with hl1
  have hmode : ∀ n, mainECellCrossCarrier U (fun x => -g n x) (rcv (μ n)) =
      2 * volumeAverage (openCubeSet U) (fun x => vecDot (rem n x) (rcv (μ n) x)) -
        2 * (l0 * (A n * μ n 0) + l1 * (A n * μ n 1)) := by
    intro n
    rw [hotCov_cross_decomp U (g n) (rem n) X (rcv (μ n)) (A n) (hrem n) (hg n) hX (hrcv _),
      hell (μ n)]
    ring
  have hsum := (hP.mul_left 2).sub (((hM 0).mul_left l0).add ((hM 1).mul_left l1) |>.mul_left 2)
  convert hsum using 1
  · funext n
    exact hmode n
  · rw [hell M]
    ring

end

end ASDExplicitGamma.Main
