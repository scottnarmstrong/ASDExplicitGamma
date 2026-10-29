module

public import ASDExplicitGamma.Main.HotCovCarrier
public import ASDExplicitGamma.Main.HotCovRemSeries
public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy
public import ASDExplicitGamma.Native.OldSignedTopDirectionalWeakProxy
public import ASDExplicitGamma.Native.OldSignedAveragePairing
public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget

/-! MA-E-COVARIANCE, step 13: cellwise K/P duality for the affine receivers, with the
receiver's weak size paid by the directional proxy of its own cell frame. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- Weak size of the top-load receiver `-B_U^rec ν`: paid by the directional proxy of
the cell frame. -/
theorem hotCov_topRcv_weak_le (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    vectorWeakHaarEnergy U.val (hotCovTopRcv Q d nu sigma hnu hsigma k U ν) ≤
      oldSignedDirectionalProxy U.val
        (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) ν := by
  have h := old_signed_bottom_directional_weak_bound U.val nu sigma hnu hsigma
    (hotCovCellCoef Q d k U) ν
  dsimp only at h
  have hneg : vectorWeakHaarEnergy U.val (hotCovTopRcv Q d nu sigma hnu hsigma k U ν) =
      vectorWeakHaarEnergy U.val (fun x =>
        (oldSignedDualReflection U.val nu sigma (hotCovCellCoef Q d k U)
          (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U)
            (0, ν)) x).1 - ν) := by
    have hfun : hotCovTopRcv Q d nu sigma hnu hsigma k U ν = fun x => fun i => -(
        (oldSignedDualReflection U.val nu sigma (hotCovCellCoef Q d k U)
          (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U)
            (0, ν)) x).1 - ν) i := by
      funext x i
      rfl
    rw [hfun]
    exact ASDExplicitGamma.Inverse.vectorWeakHaarEnergy_neg_hot U.val _
  rw [hneg]
  exact le_trans (le_add_of_nonneg_left (vectorWeakHaarEnergy_nonneg _ _)) h

/-- Weak size of the bottom-load receiver `-T_U ν`. -/
theorem hotCov_botRcv_weak_le (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    vectorWeakHaarEnergy U.val (hotCovBotRcv Q d nu sigma hnu hsigma k U ν) ≤
      oldSignedDirectionalProxy U.val
        (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) ν := by
  have h := old_signed_top_directional_weak_bound U.val nu sigma hnu hsigma
    (hotCovCellCoef Q d k U) ν
  dsimp only at h
  have hneg : vectorWeakHaarEnergy U.val (hotCovBotRcv Q d nu sigma hnu hsigma k U ν) =
      vectorWeakHaarEnergy U.val (fun x =>
        (oldSignedDualReflection U.val nu sigma (hotCovCellCoef Q d k U)
          (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U)
            (ν, 0)) x).1) := by
    have hfun : hotCovBotRcv Q d nu sigma hnu hsigma k U ν = fun x => fun i => -(
        (oldSignedDualReflection U.val nu sigma (hotCovCellCoef Q d k U)
          (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U)
            (ν, 0)) x).1) i := by
      funext x i
      rfl
    rw [hfun]
    exact ASDExplicitGamma.Inverse.vectorWeakHaarEnergy_neg_hot U.val _
  rw [hneg]
  exact le_trans (le_add_of_nonneg_left (vectorWeakHaarEnergy_nonneg _ _)) h

theorem hotCov_source_memL2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) :
    MemVectorL2 (openCubeSet U)
      (fun x => (hotPatchSource Q d d nu sigma hnu hsigma k b L n P x).2) :=
  memVectorL2_snd_of_memBlockL2
    ((hot_patch_source_memL2 Q d d nu sigma hnu hsigma k b L n P).mono_measure
      (Measure.restrict_mono_set volume hU))

theorem hotCov_rem_memL2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q d) :
    MemVectorL2 (openCubeSet U) (hotCovRem Q d nu sigma hnu hsigma k b L n P U) := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hg := hotCov_source_memL2 Q d nu sigma hnu hsigma k b L n P U hsub
  have hz := hotCov_zfield_memL2 Q d (hotPatchPotential Q d nu sigma hnu hsigma k P)
  have hJz := hotCov_memVectorL2_quarterTurn
    (hz.mono_measure (Measure.restrict_mono_set volume hsub))
  have hc : MemVectorL2 (openCubeSet U) (fun x =>
      cubeAverage U (hotCovPsi b L n) • planarQuarterTurn
        (hotCovZ Q d nu sigma hnu hsigma k P x)) := by
    apply hotCov_memVectorL2_of_coord
    intro i
    have := (memScalarL2_coord_of_memVectorL2 hJz i).const_mul (cubeAverage U (hotCovPsi b L n))
    simpa [smul_eq_mul, hotCovZ] using this
  exact hg.add hc

/-- K/P duality of a residual-source mode against any receiver field. -/
theorem hotCov_rem_pair_bound (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q d) (e : Vec 2 → Vec 2)
    (he : MemVectorL2 (openCubeSet U) e) :
    |volumeAverage (openCubeSet U) (fun x =>
        vecDot (hotCovRem Q d nu sigma hnu hsigma k b L n P U x) (e x))| ≤
      vectorWeakHaarNorm U e *
        vectorPositiveHaarNorm U (hotCovRem Q d nu sigma hnu hsigma k b L n P U) := by
  have h := old_signed_vector_average_pairing_bound U e
    (hotCovRem Q d nu sigma hnu hsigma k b L n P U) he
    (hotCov_rem_memL2 Q d nu sigma hnu hsigma k b L n P U hU)
    (hot_cov_rem_positive_series Q d nu sigma hnu hsigma k b L n P U hU)
  have hsym : volumeAverage (openCubeSet U) (fun x =>
      vecDot (hotCovRem Q d nu sigma hnu hsigma k b L n P U x) (e x)) =
      volumeAverage (openCubeSet U) (fun x =>
        vecDot (e x) (hotCovRem Q d nu sigma hnu hsigma k b L n P U x)) := by
    congr 1
    funext x
    exact vecDot_comm _ _
  rw [hsym]
  exact h

end

end ASDExplicitGamma.Main

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- The cell-mean coordinates of a finite-parent flat coordinate are square summable. -/
theorem hotCov_flat_mean_sq_summable (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    Summable (fun n : whiteBasisIndex => (hotCovFlatMean Q b L plus U n i k) ^ 2) := by
  have hs := whiteBasis.hasSum_inner_mul_inner
    (hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)
    (hilbertCubeAverage U (hotCovFlatKernel Q b L plus i k).toFun)
  apply hs.summable.congr
  intro j
  rw [real_inner_comm (whiteBasis j), hotCov_flat_kernel_mean Q depth b L plus U hU i k j]
  ring

theorem hotCov_flat_mean_vec_sq_summable (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (plus : Bool) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i : Fin 2) :
    Summable (fun n : whiteBasisIndex => vecNormSq (hotCovFlatMeanVec Q b L plus U n i)) := by
  have h0 := hotCov_flat_mean_sq_summable Q depth b L plus U hU i 0
  have h1 := hotCov_flat_mean_sq_summable Q depth b L plus U hU i 1
  apply (h0.add h1).congr
  intro n
  simp [vecNormSq, vecDot, Fin.sum_univ_two, pow_two]

/-- The receiver weak sizes are square summable over the Gaussian modes. -/
theorem hotCov_rcv_weak_sq_summable_top (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (U : OldSignedCellIndex Q d) (i : Fin 2) :
    Summable (fun n : whiteBasisIndex => vectorWeakHaarEnergy U.val
      (hotCovTopRcv Q d nu sigma hnu hsigma k U (hotCovFlatMeanVec Q b L true U.val n i))) := by
  have hbound := old_signed_directional_proxy_nonneg_le U.val nu sigma hnu hsigma
    (hotCovCellCoef Q d k U)
  set C := ASDExplicitGamma.Inverse.rawWeakTraceProxy (lemmaVInverseDepthMax U.val
    (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)))
    (fun j => descendantsAverage U.val j (fun V => traceDefect (openCubeSet V)
      (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) 1)) with hC
  have hs := (hotCov_flat_mean_vec_sq_summable Q d b L true U.val U.property i).mul_left C
  refine hs.of_nonneg_of_le (fun n => vectorWeakHaarEnergy_nonneg _ _) (fun n => ?_)
  exact (hotCov_topRcv_weak_le Q d nu sigma hnu hsigma k U _).trans (by
    have := (hbound (hotCovFlatMeanVec Q b L true U.val n i)).2
    simpa [mul_comm] using this)

theorem hotCov_rcv_weak_sq_summable_bot (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (U : OldSignedCellIndex Q d) (i : Fin 2) :
    Summable (fun n : whiteBasisIndex => vectorWeakHaarEnergy U.val
      (hotCovBotRcv Q d nu sigma hnu hsigma k U (hotCovFlatMeanVec Q b L false U.val n i))) := by
  have hbound := old_signed_directional_proxy_nonneg_le U.val nu sigma hnu hsigma
    (hotCovCellCoef Q d k U)
  set C := ASDExplicitGamma.Inverse.rawWeakTraceProxy (lemmaVInverseDepthMax U.val
    (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)))
    (fun j => descendantsAverage U.val j (fun V => traceDefect (openCubeSet V)
      (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) 1)) with hC
  have hs := (hotCov_flat_mean_vec_sq_summable Q d b L false U.val U.property i).mul_left C
  refine hs.of_nonneg_of_le (fun n => vectorWeakHaarEnergy_nonneg _ _) (fun n => ?_)
  exact (hotCov_botRcv_weak_le Q d nu sigma hnu hsigma k U _).trans (by
    have := (hbound (hotCovFlatMeanVec Q b L false U.val n i)).2
    simpa [mul_comm] using this)

end

end ASDExplicitGamma.Main

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- On a single cell and load, the residual source positive energies are summable
over the modes. -/
theorem hotCov_rem_sq_summable (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d) (c : BlockCoord 2) :
    Summable (fun n : whiteBasisIndex => vectorPositiveHaarEnergy U
      (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U x)) := by
  classical
  have hs := (hot_cov_rem_size_bound Q d nu sigma hnu hsigma k b L hL hmesh).1
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q d).card : ℝ) := by
    have hne : (descendantsAtDepth Q d).Nonempty := ⟨U, hU⟩
    exact_mod_cast hne.card_pos
  refine (hs.mul_left ((descendantsAtDepth Q d).card : ℝ)).of_nonneg_of_le
    (fun n => vectorPositiveHaarEnergy_nonneg _ _) (fun n => ?_)
  have h1 : vectorPositiveHaarEnergy U
      (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U x) ≤
      ((descendantsAtDepth Q d).card : ℝ) * descendantsAverage Q d (fun V =>
        vectorPositiveHaarEnergy V
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) V x)) := by
    unfold descendantsAverage
    rw [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul]
    exact Finset.single_le_sum (f := fun V => vectorPositiveHaarEnergy V
      (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) V x))
      (fun V _ => vectorPositiveHaarEnergy_nonneg _ _) hU
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hcard.le)
  exact Finset.single_le_sum (f := fun c' => descendantsAverage Q d (fun V =>
      vectorPositiveHaarEnergy V
        (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c') V x)))
    (fun c' _ => descendantsAverage_nonneg Q d _ (fun V _ => vectorPositiveHaarEnergy_nonneg _ _))
    (Finset.mem_univ c)

end

end ASDExplicitGamma.Main
