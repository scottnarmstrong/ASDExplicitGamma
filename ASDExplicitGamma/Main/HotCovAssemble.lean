module

public import ASDExplicitGamma.Main.HotCovCellSeries
public import ASDExplicitGamma.Main.HotCovPairedDrop
public import ASDExplicitGamma.Main.HotCovFlatCap

/-! MA-E-COVARIANCE, step 15: the four canonical loads, assembled.  For the load
`c` (top `i` or bottom `i`) the receiver, sign flag, pair load and pairing field are
selected by `c`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- Receiver of the load `c`: `-B_U^rec` for a top load, `-T_U` for a bottom load. -/
def hotCovRcvC (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (c : BlockCoord 2) (U : OldSignedCellIndex Q d)
    (ν : Vec 2) : Vec 2 → Vec 2 :=
  match c with
  | Sum.inl _ => hotCovTopRcv Q d nu sigma hnu hsigma k U ν
  | Sum.inr _ => hotCovBotRcv Q d nu sigma hnu hsigma k U ν

/-- The sign flag of the finite-parent flat family seen by the load `c`. -/
def hotCovPlusC : BlockCoord 2 → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- The load index `i` of `c`. -/
def hotCovIdxC : BlockCoord 2 → Fin 2
  | Sum.inl i => i
  | Sum.inr i => i

/-- The opposite canonical load `(0,ν)` / `(ν,0)` whose drop reciprocal block pays the
principal term of the load `c`. -/
def hotCovPairLoadC : BlockCoord 2 → Vec 2 → BlockVec 2
  | Sum.inl _, ν => (0, ν)
  | Sum.inr _, ν => (ν, 0)

/-- Per-load affine cross of the hot trial. -/
def hotCovAffCrossC (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (c : BlockCoord 2) (n : whiteBasisIndex) (U : OldSignedCellIndex Q d) : ℝ :=
  match c with
  | Sum.inl i => hotCovTopAffCross Q d nu sigma hnu hsigma k b L n i U
  | Sum.inr i => hotCovBotAffCross Q d nu sigma hnu hsigma k b L n i U

theorem hotCovAffMode_eq_sum (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (U : OldSignedCellIndex Q d) :
    hotCovAffMode Q d nu sigma hnu hsigma k b L n U =
      ∑ c : BlockCoord 2, hotCovAffCrossC Q d nu sigma hnu hsigma k b L c n U := by
  rw [Fintype.sum_sum_type]
  rfl

theorem hotCovRcvC_memL2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (c : BlockCoord 2) (U : OldSignedCellIndex Q d)
    (ν : Vec 2) :
    MemVectorL2 (openCubeSet U.val) (hotCovRcvC Q d nu sigma hnu hsigma k c U ν) := by
  cases c
  · exact hotCov_topRcv_memL2 Q d nu sigma hnu hsigma k U ν
  · exact hotCov_botRcv_memL2 Q d nu sigma hnu hsigma k U ν

theorem hotCovRcvC_linear (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (c : BlockCoord 2) (U : OldSignedCellIndex Q d)
    (ν : Vec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      hotCovRcvC Q d nu sigma hnu hsigma k c U ν x =
        ν 0 • hotCovRcvC Q d nu sigma hnu hsigma k c U (basisVec 0) x +
          ν 1 • hotCovRcvC Q d nu sigma hnu hsigma k c U (basisVec 1) x := by
  cases c
  · exact hotCov_topRcv_linear Q d nu sigma hnu hsigma k U ν
  · exact hotCov_botRcv_linear Q d nu sigma hnu hsigma k U ν

theorem hotCovRcvC_weak_sq_summable (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (c : BlockCoord 2) (U : OldSignedCellIndex Q d) :
    Summable (fun n : whiteBasisIndex => vectorWeakHaarEnergy U.val
      (hotCovRcvC Q d nu sigma hnu hsigma k c U
        (hotCovFlatMeanVec Q b L (hotCovPlusC c) U.val n (hotCovIdxC c)))) := by
  cases c
  · exact hotCov_rcv_weak_sq_summable_top Q d nu sigma hnu hsigma k b L U _
  · exact hotCov_rcv_weak_sq_summable_bot Q d nu sigma hnu hsigma k b L U _

/-- The exact cell-level mode series of the affine carrier of one load. -/
theorem hotCov_cell_series_C (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1)
    (U : OldSignedCellIndex Q d) (c : BlockCoord 2) :
    |hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) (hotCovPlusC c)
        (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U)| ≤
      Real.sqrt (∑' n : whiteBasisIndex, vectorPositiveHaarEnergy U.val
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x)) *
        Real.sqrt (∑' n : whiteBasisIndex, vectorWeakHaarEnergy U.val
          (hotCovRcvC Q d nu sigma hnu hsigma k c U
            (hotCovFlatMeanVec Q b L (hotCovPlusC c) U.val n (hotCovIdxC c)))) ∧
    HasSum (fun n : whiteBasisIndex =>
        hotCovAffCrossC Q d nu sigma hnu hsigma k b L c n U)
      (2 * hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) (hotCovPlusC c)
          (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U) -
        b ^ 2 * hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
          (hotCovRcvC Q d nu sigma hnu hsigma k c U (hotCovJcol (hotCovIdxC c))) -
        2 * hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
          (hotCovRcvC Q d nu sigma hnu hsigma k c U
            (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c)))) := by
  have h := hotCov_cell_series_generic Q d nu sigma hnu hsigma k b L hL hmesh U c
    (hotCovPlusC c) (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U)
    (hotCovRcvC_memL2 Q d nu sigma hnu hsigma k c U)
    (hotCovRcvC_linear Q d nu sigma hnu hsigma k c U)
    (hotCovRcvC_weak_sq_summable Q d nu sigma hnu hsigma k b L c U)
  refine ⟨h.1, ?_⟩
  cases c
  · exact h.2
  · exact h.2

/-- Cell average of the residual cross series over the four loads. -/
def hotCovResTotal (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2,
    hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) (hotCovPlusC c)
      (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U))

/-- Cell average of the principal pairing `<J z, rcv(J e_i)>` over the four loads. -/
def hotCovPrinTotal (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2,
    hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
      (hotCovRcvC Q d nu sigma hnu hsigma k c U (hotCovJcol (hotCovIdxC c))))

/-- Cell average of the covariance-error pairing `<J z, rcv(ε_i)>` over the four loads. -/
def hotCovErrTotal (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2,
    hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
      (hotCovRcvC Q d nu sigma hnu hsigma k c U
        (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))))

/-- EXACT decomposition of the affine C carrier of the hot trial into its residual-source
part, its principal `v/2` part and its covariance-error part. -/
theorem hotCov_affCarrier_decomp (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1) :
    hotCovAffCarrier Q d nu sigma hnu hsigma k b L =
      2 * hotCovResTotal Q d nu sigma hnu hsigma k b L -
        b ^ 2 * hotCovPrinTotal Q d nu sigma hnu hsigma k -
        2 * hotCovErrTotal Q d nu sigma hnu hsigma k b L := by
  classical
  have hcell (U : OldSignedCellIndex Q d) :
      HasSum (fun n => hotCovAffMode Q d nu sigma hnu hsigma k b L n U)
        (∑ c : BlockCoord 2,
          (2 * hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) (hotCovPlusC c)
              (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U) -
            b ^ 2 * hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
              (hotCovRcvC Q d nu sigma hnu hsigma k c U (hotCovJcol (hotCovIdxC c))) -
            2 * hotCovEll Q d U (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
              (hotCovRcvC Q d nu sigma hnu hsigma k c U
                (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))))) := by
    have hs := hasSum_sum (s := Finset.univ) (fun c _ =>
      (hotCov_cell_series_C Q d nu sigma hnu hsigma k b L hL hmesh U c).2)
    convert hs using 1
    funext n
    exact hotCovAffMode_eq_sum Q d nu sigma hnu hsigma k b L n U
  have hser := old_signed_cell_average_series Q d
    (fun n U => hotCovAffMode Q d nu sigma hnu hsigma k b L n U) (fun U => (hcell U).summable)
  unfold hotCovAffCarrier
  rw [hser.2]
  have hval : (fun U : OldSignedCellIndex Q d => ∑' n, hotCovAffMode Q d nu sigma hnu hsigma k b L n U) =
      fun U => 2 * (∑ c : BlockCoord 2, hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c)
            (hotCovPlusC c) (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U)) -
        b ^ 2 * (∑ c : BlockCoord 2, hotCovEll Q d U
          (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
          (hotCovRcvC Q d nu sigma hnu hsigma k c U (hotCovJcol (hotCovIdxC c)))) -
        2 * (∑ c : BlockCoord 2, hotCovEll Q d U
          (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
          (hotCovRcvC Q d nu sigma hnu hsigma k c U
            (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c)))) := by
    funext U
    rw [(hcell U).tsum_eq]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hval, old_signed_cell_average_sub, old_signed_cell_average_sub, old_signed_cell_average_mul,
    old_signed_cell_average_mul, old_signed_cell_average_mul]
  rfl

end

end ASDExplicitGamma.Main
