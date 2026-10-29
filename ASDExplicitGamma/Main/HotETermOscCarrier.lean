module

public import ASDExplicitGamma.Native.OldSignedAveragePairing
public import ASDExplicitGamma.Native.OldSignedQ3SourceAdmissibility
public import ASDExplicitGamma.Main.EOscillationJointProfile
public import ASDExplicitGamma.Native.OldSignedFlatProfiles
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy
public import ASDExplicitGamma.Native.OldSignedSpatialSeriesBound
public import ASDExplicitGamma.Main.ETermOscillatoryReceiver

/-! Generic-source oscillatory carriers of the mixed C-group and their `2 d q` bill: copies
of the original-trial modules with the localized source field `H n P` as a parameter. The only
source properties used are membership in `L²` and summability of the positive Haar series of
its coordinates on each cell. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

/-- The actual complete positive size of a localized source family on one cell. -/
def hotSourceSize (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (U : TriadicCube 2) : ℝ :=
  Real.sqrt (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2,
    vectorPositiveHaarNorm U (fun x => (H n (blockBasis c) x).2) ^ 2)

/-- Oscillatory top contribution, the exact remainder after removing the
actual cell-mean affine receiver. -/
noncomputable def mainECellTopOscillatoryCrossCarrierHot
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2) (n : whiteBasisIndex)
    (i : Fin 2) (U : OldSignedCellIndex Q depth) : ℝ :=
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let F := oldSignedFlatInput Q b L true n i
  let H := H n
    (oldSignedFlatLoad true i)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F
    (old_signed_flat_input_memL2 Q b L true n i)
  let eaff := mainECellTopAffineOfFlatInput U.val a hEll F
  mainECellCrossCarrier U.val (fun x => -(H x).2)
    (mainECellTopOscillatoryReceiver U.val a A F eaff)

/-- Oscillatory bottom contribution, the exact remainder after removing the
actual cell-mean affine receiver. -/
noncomputable def mainECellBottomOscillatoryCrossCarrierHot
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2) (n : whiteBasisIndex)
    (i : Fin 2) (U : OldSignedCellIndex Q depth) : ℝ :=
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let F := oldSignedFlatInput Q b L false n i
  let H := H n
    (oldSignedFlatLoad false i)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F
    (old_signed_flat_input_memL2 Q b L false n i)
  let eaff := mainECellBottomAffineOfFlatInput U.val a hEll F
  mainECellCrossCarrier U.val (fun x => -(H x).2)
    (mainECellBottomOscillatoryReceiver U.val a A F eaff)

/-- Modewise oscillatory covariance carrier over the actual top and bottom
loads. -/
noncomputable def mainECellMixedModeOscillatoryCarrierHot
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2) (n : whiteBasisIndex)
    (U : OldSignedCellIndex Q depth) : ℝ :=
  (∑ i : Fin 2,
    mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma k b L H n i U) +
  ∑ i : Fin 2,
    mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma k b L H n i U

private theorem vectorPositiveHaarNorm_neg_hot
    (U : TriadicCube 2) (f : Vec 2 → Vec 2) :
    vectorPositiveHaarNorm U (fun x => -f x) =
      vectorPositiveHaarNorm U f := by
  unfold vectorPositiveHaarNorm vectorPositiveHaarEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.neg_apply]
  exact primalEnergy_neg U (Real.sqrt 3) (fun x => f x i)

private theorem main_e_oscillatory_average_abs_bound_hot
    (U : TriadicCube 2) (f e : Vec 2 → Vec 2)
    (hf : MemVectorL2 (openCubeSet U) f)
    (he : MemVectorL2 (openCubeSet U) e)
    (hs : ∀ i : Fin 2, Summable (fun j : ℕ =>
      (Real.sqrt 3) ^ (j + 1) * energy U (cubeIncrement U (j + 1)
        (fun x => f x i)))) :
    |volumeAverage (openCubeSet U) (fun x => vecDot (f x) (e x))| ≤
      vectorWeakHaarNorm U e * vectorPositiveHaarNorm U f := by
  have h := old_signed_vector_average_pairing_bound U e f he hf hs
  have hsym : volumeAverage (openCubeSet U)
      (fun x => vecDot (f x) (e x)) =
      volumeAverage (openCubeSet U)
        (fun x => vecDot (e x) (f x)) := by
    congr 1
    funext x
    exact vecDot_comm _ _
  rw [hsym]
  exact h

/-- The actual top mixed oscillatory cross is paid by the actual localized
OLD source size and the pure-second centered reciprocal cap. -/
theorem main_e_top_oscillatory_cross_abs_bound_hot
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P))
    (hpos : ∀ (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2)
      (_hU : U ∈ descendantsAtDepth Q depth) (j : Fin 2),
      Summable (fun d : ℕ => (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => -((H n P x).2 j)))))
    (n : whiteBasisIndex) (i : Fin 2)
    (U : OldSignedCellIndex Q depth) :
    |mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma
        hnu hsigma k b L H n i U| ≤
      2 * vectorPositiveHaarNorm U.val (fun x =>
        (H n (oldSignedFlatLoad true i) x).2) *
        ((oldSignedInverseHistory U.val
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) + 1) *
          oldSignedBlockPositiveNorm U.val
            (oldSignedFlatInput Q b L true n i -
              fun _ => oldSignedBlockMean U.val
                (oldSignedFlatInput Q b L true n i))) := by
  classical
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let F := oldSignedFlatInput Q b L true n i
  let Hsrc := H n
    (oldSignedFlatLoad true i)
  let mF := oldSignedBlockMean U.val F
  let G := fun x => F x - mF
  change |mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma k
      b L H n i U| ≤
    2 * vectorPositiveHaarNorm U.val (fun x => (Hsrc x).2) *
      ((oldSignedInverseHistory U.val a + 1) * oldSignedBlockPositiveNorm U.val G)
  let hFparent := old_signed_flat_input_memL2 Q b L true n i
  let hF := hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let hG := hF.sub (memLp_const mF)
  let ZG := scalarResidualField U.val nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hG)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F hFparent
  let eaff := mainECellTopAffineOfFlatInput U.val a hEll F
  let eosc := mainECellTopOscillatoryReceiver U.val a A F eaff
  let Hloc := fun x => -(Hsrc x).2
  have hHparent := hH n (oldSignedFlatLoad true i)
  have hH := hHparent.mono_measure (Measure.restrict_mono_set volume hsub)
  have hSource : MemVectorL2 (openCubeSet U.val) Hloc :=
    (memVectorL2_snd_of_memBlockL2 hH).neg
  have hFlux : MemBlockL2 (openCubeSet U.val) (scalarCoefficientFlux a ZG) :=
    scalar_coefficient_flux_memL2 U.val a hEll (Lp.memLp ZG)
  have hCentered : MemVectorL2 (openCubeSet U.val)
      (fun x => (scalarCoefficientFlux a ZG x).2 - (G x).2) :=
    (memVectorL2_snd_of_memBlockL2 hFlux).sub
      (memVectorL2_snd_of_memBlockL2 hG)
  have hEq := main_e_top_oscillatory_receiver_eq_centered Q U.val depth
    U.property nu sigma hnu hsigma k b L n i
  have hReceiver : MemVectorL2 (openCubeSet U.val) eosc :=
    hCentered.ae_eq hEq.symm
  have hParentEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hSourcePositive : ∀ j : Fin 2, Summable (fun d : ℕ =>
      (Real.sqrt 3) ^ (d + 1) * energy U.val (cubeIncrement U.val (d + 1)
        (fun x => Hloc x j))) := by
    intro j
    exact hpos n (oldSignedFlatLoad true i) U.val U.property j
  have hPair := main_e_oscillatory_average_abs_bound_hot U.val Hloc eosc
    hSource hReceiver hSourcePositive
  have hWeak := main_e_top_oscillatory_receiver_weak_bound Q U.val depth
    U.property nu sigma hnu hsigma k b L n i
  have hcarrier : mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma
      hnu hsigma k b L H n i U =
      -2 * volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x)) := by
    rfl
  rw [hcarrier]
  have hAbsScale : |(-2 : ℝ) * volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x))| =
      2 * |volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x))| := by
    rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
    ring
  rw [hAbsScale]
  have hPos : 0 ≤ vectorPositiveHaarNorm U.val Hloc := Real.sqrt_nonneg _
  calc
    2 * |volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x))| ≤
      2 * (vectorWeakHaarNorm U.val eosc * vectorPositiveHaarNorm U.val Hloc) :=
        mul_le_mul_of_nonneg_left hPair (by norm_num)
    _ ≤ 2 * (((oldSignedInverseHistory U.val a + 1) *
        oldSignedBlockPositiveNorm U.val G) *
        vectorPositiveHaarNorm U.val Hloc) := by
        gcongr
    _ = 2 * vectorPositiveHaarNorm U.val (fun x => (Hsrc x).2) *
        ((oldSignedInverseHistory U.val a + 1) *
          oldSignedBlockPositiveNorm U.val G) := by
        rw [show vectorPositiveHaarNorm U.val Hloc =
          vectorPositiveHaarNorm U.val (fun x => (Hsrc x).2) by
            unfold Hloc
            exact vectorPositiveHaarNorm_neg_hot U.val
              (fun x => (Hsrc x).2)]
        ring

/-- The actual bottom mixed oscillatory cross is paid by the actual
localized OLD source size and the centered reciprocal cap. -/
theorem main_e_bottom_oscillatory_cross_abs_bound_hot
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P))
    (hpos : ∀ (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2)
      (_hU : U ∈ descendantsAtDepth Q depth) (j : Fin 2),
      Summable (fun d : ℕ => (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => -((H n P x).2 j)))))
    (n : whiteBasisIndex) (i : Fin 2)
    (U : OldSignedCellIndex Q depth) :
    |mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma
        hnu hsigma k b L H n i U| ≤
      2 * vectorPositiveHaarNorm U.val (fun x =>
        (H n (oldSignedFlatLoad false i) x).2) *
        (Real.sqrt (oldSignedInverseHistory U.val
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) *
          oldSignedResponseHistory U.val
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) *
          oldSignedBlockPositiveNorm U.val
            (oldSignedFlatInput Q b L false n i -
              fun _ => oldSignedBlockMean U.val
                (oldSignedFlatInput Q b L false n i))) := by
  classical
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let F := oldSignedFlatInput Q b L false n i
  let Hsrc := H n
    (oldSignedFlatLoad false i)
  let mF := oldSignedBlockMean U.val F
  let G := fun x => F x - mF
  change |mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma k
      b L H n i U| ≤
    2 * vectorPositiveHaarNorm U.val (fun x => (Hsrc x).2) *
      (Real.sqrt (oldSignedInverseHistory U.val a * oldSignedResponseHistory U.val a) *
        oldSignedBlockPositiveNorm U.val G)
  let hFparent := old_signed_flat_input_memL2 Q b L false n i
  let hF := hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let hG := hF.sub (memLp_const mF)
  let ZG := scalarResidualField U.val nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField hG)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F hFparent
  let eaff := mainECellBottomAffineOfFlatInput U.val a hEll F
  let eosc := mainECellBottomOscillatoryReceiver U.val a A F eaff
  let Hloc := fun x => -(Hsrc x).2
  have hHparent := hH n (oldSignedFlatLoad false i)
  have hH := hHparent.mono_measure (Measure.restrict_mono_set volume hsub)
  have hSource : MemVectorL2 (openCubeSet U.val) Hloc :=
    (memVectorL2_snd_of_memBlockL2 hH).neg
  have hFlux : MemBlockL2 (openCubeSet U.val) (scalarCoefficientFlux a ZG) :=
    scalar_coefficient_flux_memL2 U.val a hEll (Lp.memLp ZG)
  have hCentered : MemVectorL2 (openCubeSet U.val)
      (fun x => (scalarCoefficientFlux a ZG x).2) :=
    memVectorL2_snd_of_memBlockL2 hFlux
  have hEq := main_e_bottom_oscillatory_receiver_eq_centered Q U.val depth
    U.property nu sigma hnu hsigma k b L n i
  have hReceiver : MemVectorL2 (openCubeSet U.val) eosc := by
    have hNeg : MemVectorL2 (openCubeSet U.val)
        (fun x => -(scalarCoefficientFlux a ZG x).2) := hCentered.neg
    exact hNeg.ae_eq hEq.symm
  have hParentEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hSourcePositive : ∀ j : Fin 2, Summable (fun d : ℕ =>
      (Real.sqrt 3) ^ (d + 1) * energy U.val (cubeIncrement U.val (d + 1)
        (fun x => Hloc x j))) := by
    intro j
    exact hpos n (oldSignedFlatLoad false i) U.val U.property j
  have hPair := main_e_oscillatory_average_abs_bound_hot U.val Hloc eosc
    hSource hReceiver hSourcePositive
  have hWeak := main_e_bottom_oscillatory_receiver_weak_bound Q U.val depth
    U.property nu sigma hnu hsigma k b L n i
  have hcarrier : mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma
      hnu hsigma k b L H n i U =
      -2 * volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x)) := by
    rfl
  rw [hcarrier]
  have hAbsScale : |(-2 : ℝ) * volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x))| =
      2 * |volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x))| := by
    rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
    ring
  rw [hAbsScale]
  have hPos : 0 ≤ vectorPositiveHaarNorm U.val Hloc := Real.sqrt_nonneg _
  calc
    2 * |volumeAverage (openCubeSet U.val)
        (fun x => vecDot (Hloc x) (eosc x))| ≤
      2 * (vectorWeakHaarNorm U.val eosc * vectorPositiveHaarNorm U.val Hloc) :=
        mul_le_mul_of_nonneg_left hPair (by norm_num)
    _ ≤ 2 * (Real.sqrt (oldSignedInverseHistory U.val a *
        oldSignedResponseHistory U.val a) * oldSignedBlockPositiveNorm U.val G *
        vectorPositiveHaarNorm U.val Hloc) := by
        gcongr
    _ = 2 * vectorPositiveHaarNorm U.val (fun x => (Hsrc x).2) *
        (Real.sqrt (oldSignedInverseHistory U.val a *
          oldSignedResponseHistory U.val a) * oldSignedBlockPositiveNorm U.val G) := by
        rw [show vectorPositiveHaarNorm U.val Hloc =
          vectorPositiveHaarNorm U.val (fun x => (Hsrc x).2) by
            unfold Hloc
            exact vectorPositiveHaarNorm_neg_hot U.val
              (fun x => (Hsrc x).2)]
        ring

/-- The actual oscillatory part of the mixed C-group is summable over all
q3 modes and pays the exact source-size times joint-profile bill on each
source cell. -/
theorem main_e_actual_oscillatory_cross_2dq_hot
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P))
    (hpos : ∀ (n : whiteBasisIndex) (P : BlockVec 2) (U : TriadicCube 2)
      (_hU : U ∈ descendantsAtDepth Q depth) (j : Fin 2),
      Summable (fun d : ℕ => (Real.sqrt 3) ^ (d + 1) * energy U (cubeIncrement U (d + 1)
        (fun x => -((H n P x).2 j)))))
    (hsrc : ∀ (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q depth),
      Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
        vectorPositiveHaarNorm U (fun x => (H n (blockBasis c) x).2) ^ 2))
    (U : OldSignedCellIndex Q depth) :
    Summable (fun n : whiteBasisIndex =>
      mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma
        hnu hsigma k b L H n U) ∧
    |∑' n : whiteBasisIndex,
      mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma
        hnu hsigma k b L H n U| ≤
      2 * hotSourceSize H U.val *
        mainOldJointOscillationProfile Q U.val nu sigma k b L := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let I := oldSignedInverseHistory U.val a
  let R := oldSignedResponseHistory U.val a
  let source := fun (n : whiteBasisIndex) (c : BlockCoord 2) =>
    vectorPositiveHaarNorm U.val (fun x =>
      (H n
        (blockBasis c) x).2)
  let plusOsc := fun (n : whiteBasisIndex) (i : Fin 2) =>
    oldSignedBlockPositiveNorm U.val
      (oldSignedFlatInput Q b L true n i -
        fun _ => oldSignedBlockMean U.val (oldSignedFlatInput Q b L true n i))
  let minusOsc := fun (n : whiteBasisIndex) (i : Fin 2) =>
    oldSignedBlockPositiveNorm U.val
      (oldSignedFlatInput Q b L false n i -
        fun _ => oldSignedBlockMean U.val (oldSignedFlatInput Q b L false n i))
  let cap := fun (n : whiteBasisIndex) (c : BlockCoord 2) =>
    match c with
    | Sum.inl i => 2 * ((I + 1) * plusOsc n i)
    | Sum.inr i => 2 * (Real.sqrt (I * R) * minusOsc n i)
  let cellCross := fun (n : whiteBasisIndex) (c : BlockCoord 2) =>
    match c with
    | Sum.inl i => mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma
        hnu hsigma k b L H n i U
    | Sum.inr i => mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma
        hnu hsigma k b L H n i U
  have hI : 0 ≤ I := by
    dsimp [I, a]
    exact lemmaVInverseHistory_nonneg U.val _
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hR : 0 ≤ R := by
    dsimp [R, a]
    exact ENNReal.toReal_nonneg
  have hIR : 0 ≤ I * R := mul_nonneg hI hR
  have hsource : ∀ n c, 0 ≤ source n c := by
    intro n c
    exact Real.sqrt_nonneg _
  have hcap : ∀ n c, 0 ≤ cap n c := by
    intro n c
    cases c with
    | inl i =>
        have hosc : 0 ≤ plusOsc n i := by
          dsimp [plusOsc]
          exact Real.sqrt_nonneg _
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (mul_nonneg (add_nonneg hI (by norm_num)) hosc)
    | inr i =>
        have hosc : 0 ≤ minusOsc n i := by
          dsimp [minusOsc]
          exact Real.sqrt_nonneg _
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (mul_nonneg (Real.sqrt_nonneg _) hosc)
  have hsourceSeries : Summable (fun n : whiteBasisIndex =>
      ∑ c : BlockCoord 2, source n c ^ 2) := by
    simpa [source] using hsrc U.val U.property
  have hplusSeries := old_signed_flat_oscillation_budget_series
    Q depth b L true U.val U.property
  have hminusSeries := old_signed_flat_oscillation_budget_series
    Q depth b L false U.val U.property
  have hcapPoint (n : whiteBasisIndex) :
      (∑ c : BlockCoord 2, cap n c ^ 2) =
        4 * (I + 1) ^ 2 * ∑ i : Fin 2, plusOsc n i ^ 2 +
          4 * (I * R) * ∑ i : Fin 2, minusOsc n i ^ 2 := by
    rw [Fintype.sum_sum_type]
    change (∑ i : Fin 2, (2 * ((I + 1) * plusOsc n i)) ^ 2) +
      ∑ i : Fin 2, (2 * (Real.sqrt (I * R) * minusOsc n i)) ^ 2 = _
    have htop : (∑ i : Fin 2, (2 * ((I + 1) * plusOsc n i)) ^ 2) =
        4 * (I + 1) ^ 2 * ∑ i : Fin 2, plusOsc n i ^ 2 := by
      calc
        _ = ∑ i : Fin 2, 4 * (I + 1) ^ 2 * plusOsc n i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hbottom : (∑ i : Fin 2,
        (2 * (Real.sqrt (I * R) * minusOsc n i)) ^ 2) =
        4 * (I * R) * ∑ i : Fin 2, minusOsc n i ^ 2 := by
      calc
        _ = ∑ i : Fin 2, 4 * (I * R) * minusOsc n i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [mul_pow, Real.sq_sqrt hIR]
          ring
        _ = _ := by rw [Finset.mul_sum]
    rw [htop, hbottom]
  have hcapSeries : Summable (fun n : whiteBasisIndex =>
      ∑ c : BlockCoord 2, cap n c ^ 2) := by
    have hp := hplusSeries.mul_left (4 * (I + 1) ^ 2)
    have hm := hminusSeries.mul_left (4 * (I * R))
    have hsum := hp.add hm
    simpa only [hcapPoint] using hsum
  have hplusNonneg : 0 ≤ ∑' n : whiteBasisIndex,
      ∑ i : Fin 2, plusOsc n i ^ 2 :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hminusNonneg : 0 ≤ ∑' n : whiteBasisIndex,
      ∑ i : Fin 2, minusOsc n i ^ 2 :=
    tsum_nonneg (fun n => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hplusSq :
      oldSignedFlatOscillationSize Q U.val b L true ^ 2 =
        ∑' n : whiteBasisIndex, ∑ i : Fin 2, plusOsc n i ^ 2 := by
    unfold oldSignedFlatOscillationSize
    exact Real.sq_sqrt hplusNonneg
  have hminusSq :
      oldSignedFlatOscillationSize Q U.val b L false ^ 2 =
        ∑' n : whiteBasisIndex, ∑ i : Fin 2, minusOsc n i ^ 2 := by
    unfold oldSignedFlatOscillationSize
    exact Real.sq_sqrt hminusNonneg
  have hcapTsum :
      (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, cap n c ^ 2) =
        4 * ((I + 1) ^ 2 * oldSignedFlatOscillationSize Q U.val b L true ^ 2 +
          I * R * oldSignedFlatOscillationSize Q U.val b L false ^ 2) := by
    rw [show (fun n : whiteBasisIndex => ∑ c : BlockCoord 2, cap n c ^ 2) =
        (fun n => 4 * (I + 1) ^ 2 * ∑ i : Fin 2, plusOsc n i ^ 2 +
          4 * (I * R) * ∑ i : Fin 2, minusOsc n i ^ 2) by
          funext n
          exact hcapPoint n]
    rw [Summable.tsum_add (hplusSeries.mul_left (4 * (I + 1) ^ 2))
      (hminusSeries.mul_left (4 * (I * R))), tsum_mul_left, tsum_mul_left,
      ← hplusSq, ← hminusSq]
    ring
  have hcapNorm :
      Real.sqrt (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, cap n c ^ 2) =
        2 * mainOldJointOscillationProfile Q U.val nu sigma k b L := by
    rw [hcapTsum]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show Real.sqrt (4 : ℝ) = 2 by norm_num]
    rfl
  have hcellTop (n : whiteBasisIndex) (i : Fin 2) :
      cellCross n (Sum.inl i) =
        mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma
          k b L H n i U := rfl
  have hsourceTop (n : whiteBasisIndex) (i : Fin 2) :
      source n (Sum.inl i) = vectorPositiveHaarNorm U.val (fun x =>
        (H n
          (oldSignedFlatLoad true i) x).2) := rfl
  have hcapTop (n : whiteBasisIndex) (i : Fin 2) :
      cap n (Sum.inl i) = 2 * ((I + 1) * oldSignedBlockPositiveNorm U.val
        (oldSignedFlatInput Q b L true n i -
          fun _ => oldSignedBlockMean U.val (oldSignedFlatInput Q b L true n i))) := rfl
  have hcellBottom (n : whiteBasisIndex) (i : Fin 2) :
      cellCross n (Sum.inr i) =
        mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma
          k b L H n i U := rfl
  have hsourceBottom (n : whiteBasisIndex) (i : Fin 2) :
      source n (Sum.inr i) = vectorPositiveHaarNorm U.val (fun x =>
        (H n
          (oldSignedFlatLoad false i) x).2) := rfl
  have hcapBottom (n : whiteBasisIndex) (i : Fin 2) :
      cap n (Sum.inr i) = 2 * (Real.sqrt (I * R) * oldSignedBlockPositiveNorm U.val
        (oldSignedFlatInput Q b L false n i -
          fun _ => oldSignedBlockMean U.val (oldSignedFlatInput Q b L false n i))) := rfl
  have hCellHistories := old_signed_cell_histories Q U.val
    (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
    nu sigma hnu hsigma k
  have hInvCell :
      oldSignedInverseHistory U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) =
      oldSignedInverseHistory U.val (responseFramePlanarCoefficientField nu sigma k) := by
    simpa using hCellHistories.1
  have hRespCell :
      oldSignedResponseHistory U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) =
      oldSignedResponseHistory U.val (responseFramePlanarCoefficientField nu sigma k) := by
    simpa using hCellHistories.2.1
  have hbound (n : whiteBasisIndex) (c : BlockCoord 2) :
      |cellCross n c| ≤ source n c * cap n c := by
    cases c with
    | inl i =>
        rw [hcellTop, hsourceTop, hcapTop]
        have hc := main_e_top_oscillatory_cross_abs_bound_hot Q depth nu sigma hnu hsigma k b L H hH hpos n i U
        calc
          |mainECellTopOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma
              k b L H n i U| ≤
            2 * vectorPositiveHaarNorm U.val (fun x =>
              (H n
                (oldSignedFlatLoad true i) x).2) *
              ((oldSignedInverseHistory U.val
                  (responseFramePlanarCoefficientField nu sigma
                    (oldSignedCellCoefficient Q U.val
                      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) + 1) *
                oldSignedBlockPositiveNorm U.val
                  (oldSignedFlatInput Q b L true n i -
                    fun _ => oldSignedBlockMean U.val
                      (oldSignedFlatInput Q b L true n i))) := hc
          _ = _ := by
            dsimp only [I, a]
            rw [hInvCell]
            ring_nf
    | inr i =>
        rw [hcellBottom, hsourceBottom, hcapBottom]
        have hc := main_e_bottom_oscillatory_cross_abs_bound_hot Q depth nu sigma hnu hsigma k b L H hH hpos n i U
        calc
          |mainECellBottomOscillatoryCrossCarrierHot Q depth nu sigma hnu hsigma
              k b L H n i U| ≤
            2 * vectorPositiveHaarNorm U.val (fun x =>
              (H n
                (oldSignedFlatLoad false i) x).2) *
              (Real.sqrt (oldSignedInverseHistory U.val
                  (responseFramePlanarCoefficientField nu sigma
                    (oldSignedCellCoefficient Q U.val
                      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)) *
                oldSignedResponseHistory U.val
                  (responseFramePlanarCoefficientField nu sigma
                    (oldSignedCellCoefficient Q U.val
                      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))) *
                oldSignedBlockPositiveNorm U.val
                  (oldSignedFlatInput Q b L false n i -
                    fun _ => oldSignedBlockMean U.val
                      (oldSignedFlatInput Q b L false n i))) := hc
          _ = _ := by
            dsimp only [I, R, a]
            rw [hInvCell, hRespCell]
            ring_nf
  have hbudget := old_signed_load_series_pairing_budget source cap cellCross
    hsource hcap hsourceSeries hcapSeries hbound
  have hcarrier (n : whiteBasisIndex) :
      (∑ c : BlockCoord 2, cellCross n c) =
        mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma hnu hsigma k b L H n U := by
    rw [Fintype.sum_sum_type]
    simp [cellCross, mainECellMixedModeOscillatoryCarrierHot,
      mainECellTopOscillatoryCrossCarrierHot,
      mainECellBottomOscillatoryCrossCarrierHot]
  have hseries : Summable (fun n : whiteBasisIndex =>
      mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma hnu hsigma k b L H n U) := by
    simpa only [hcarrier] using hbudget.1
  refine ⟨hseries, ?_⟩
  have htsum :
      (∑' n : whiteBasisIndex,
        mainECellMixedModeOscillatoryCarrierHot Q depth nu sigma hnu hsigma k b L H n U) =
        ∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, cellCross n c :=
    tsum_congr (fun n => (hcarrier n).symm)
  rw [htsum]
  calc
    |∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, cellCross n c| ≤
        Real.sqrt (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, source n c ^ 2) *
          Real.sqrt (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, cap n c ^ 2) :=
      hbudget.2
    _ = 2 * hotSourceSize H U.val *
        mainOldJointOscillationProfile Q U.val nu sigma k b L := by
      rw [show Real.sqrt (∑' n : whiteBasisIndex,
          ∑ c : BlockCoord 2, source n c ^ 2) =
          hotSourceSize H U.val by rfl,
        hcapNorm]
      ring

end
end ASDExplicitGamma.Main
