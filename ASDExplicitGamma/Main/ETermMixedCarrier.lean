module

public import ASDExplicitGamma.Native.OldSignedMixedPairing
public import ASDExplicitGamma.Native.OldSignedCellCrossPairing
public import ASDExplicitGamma.Native.OldSignedCanonicalPotentials
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Native.OldSignedMixedPartition
public import ASDExplicitGamma.Native.OldSignedTrialTerms
public import ASDExplicitGamma.Native.OldSignedGlobalMixedFeedback

/-! The actual source/reciprocal cross has an affine receiver and an
oscillatory receiver. This file records their exact split before either
carrier is estimated or assigned to an E-term row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian

noncomputable section

/-- The actual reciprocal defect of a patched top field against its flat
source input, on one source cell. -/
def mainECellTopReciprocalDefect (_U : TriadicCube 2)
    (a : CoeffField 2) (A F : Vec 2 → BlockVec 2) : Vec 2 → Vec 2 :=
  fun x => (scalarCoefficientFlux a A x).2 - (F x).2

/-- The actual signed reciprocal defect on a bottom load. -/
def mainECellBottomReciprocalDefect (_U : TriadicCube 2)
    (a : CoeffField 2) (A F : Vec 2 → BlockVec 2) : Vec 2 → Vec 2 :=
  fun x => -((scalarCoefficientFlux a A x).2 - (F x).2)

/-- The top affine receiving error `-B_U^rec mplus`, represented by the
actual reciprocal gradient of the local canonical minimizer for the
cell-constant bottom load. -/
def mainECellTopAffineReceiver (U : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a) (mplus : Vec 2) :
    Vec 2 → Vec 2 :=
  fun x => -((scalarCoefficientFlux a
    (oldSignedCanonicalAffineField U a hEll (0, mplus)) x).2 - mplus)

/-- The bottom affine receiving error `-T_U mminus`, represented by the
actual reciprocal gradient of the local canonical minimizer for the
cell-constant top load. -/
def mainECellBottomAffineReceiver (U : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a) (mminus : Vec 2) :
    Vec 2 → Vec 2 :=
  fun x => -(scalarCoefficientFlux a
    (oldSignedCanonicalAffineField U a hEll (mminus, 0)) x).2

/-- Top affine receiver. The native top flat input has mean
`(0,-mplus)` because it is `(0,-Fplus)`; negate that actual mean to recover
the source's `mplus = average_U Fplus` before applying `-B_U^rec mplus`. -/
noncomputable def mainECellTopAffineOfFlatInput (U : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a)
    (F : Vec 2 → BlockVec 2) : Vec 2 → Vec 2 :=
  mainECellTopAffineReceiver U a hEll (-(oldSignedBlockMean U F).2)

/-- Bottom affine receiver, using the actual cell mean of the
native bottom flat input `(Fminus,0)`. -/
noncomputable def mainECellBottomAffineOfFlatInput (U : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet U) a)
    (F : Vec 2 → BlockVec 2) : Vec 2 → Vec 2 :=
  mainECellBottomAffineReceiver U a hEll (oldSignedBlockMean U F).1

/-- The oscillatory remainder of the actual top receiver after removing the
source-defined affine receiver. -/
def mainECellTopOscillatoryReceiver (U : TriadicCube 2)
    (a : CoeffField 2) (A F : Vec 2 → BlockVec 2)
    (eaff : Vec 2 → Vec 2) : Vec 2 → Vec 2 :=
  mainECellTopReciprocalDefect U a A F - eaff

/-- The oscillatory remainder of the actual bottom receiver after removing
the source-defined affine receiver. -/
def mainECellBottomOscillatoryReceiver (U : TriadicCube 2)
    (a : CoeffField 2) (A F : Vec 2 → BlockVec 2)
    (eaff : Vec 2 → Vec 2) : Vec 2 → Vec 2 :=
  mainECellBottomReciprocalDefect U a A F - eaff

/-- Signed source pairing on a source cell, in the covariance-interface
convention `-2 <f',e>`. -/
def mainECellCrossCarrier (U : TriadicCube 2)
    (f e : Vec 2 → Vec 2) : ℝ :=
  -2 * volumeAverage (openCubeSet U) (fun x => vecDot (f x) (e x))

/-- The actual signed source cross splits exactly into its affine and
oscillatory receiving carriers. The integrability hypotheses are only the
three displayed scalar products needed for the integral identity. -/
theorem main_e_cell_cross_affine_oscillatory_split
    (U : TriadicCube 2) (f e eaff : Vec 2 → Vec 2)
    (hAff : IntegrableOn (fun x => vecDot (f x) (eaff x))
      (openCubeSet U) volume)
    (hOsc : IntegrableOn (fun x => vecDot (f x) ((e - eaff) x))
      (openCubeSet U) volume) :
    mainECellCrossCarrier U f e =
      mainECellCrossCarrier U f eaff +
        mainECellCrossCarrier U f (e - eaff) := by
  have hpoint :
      (fun x => vecDot (f x) (e x)) =
        (fun x => vecDot (f x) (eaff x) +
          vecDot (f x) ((e - eaff) x)) := by
    funext x
    rw [show e x = eaff x + (e - eaff) x by simp]
    exact vecDot_add_right _ _ _
  have hadd :
      (fun x => vecDot (f x) (eaff x) +
        vecDot (f x) ((e - eaff) x)) =
        (fun x => vecDot (f x) (eaff x)) +
          (fun x => vecDot (f x) ((e - eaff) x)) := rfl
  rw [mainECellCrossCarrier, mainECellCrossCarrier,
    mainECellCrossCarrier, hpoint, hadd,
    volumeAverage_add hAff hOsc]
  ring

/-- The top signed mixed pairing is exactly the actual patched source paired
with the top reciprocal defect. This is the native cell-level form of the
source covariance row. -/
theorem main_e_cell_top_mixed_pairing_identity
    (U : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet U))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet U) F)
    (g : Vec 2 → Vec 2) (hg : MemVectorL2 (openCubeSet U) g) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let A := scalarResidualField U nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF)
    let G : Vec 2 → BlockVec 2 := fun x => (0, g x)
    let hG : MemBlockL2 (openCubeSet U) G := memBlockL2_blockField MemLp.zero hg
    let R := scalarResidualField U nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hG)
    2 * (oldSignedEnergyPairing U nu sigma k A R -
      volumeAverage (openCubeSet U) (fun x => vecDot (F x).2 (g x))) =
      mainECellCrossCarrier U (fun x => -g x)
        (mainECellTopReciprocalDefect U a A F) := by
  dsimp only
  let a := responseFramePlanarCoefficientField nu sigma k
  let A := scalarResidualField U nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hF)
  let G : Vec 2 → BlockVec 2 := fun x => (0, g x)
  let hG : MemBlockL2 (openCubeSet U) G := memBlockL2_blockField MemLp.zero hg
  let R := scalarResidualField U nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hG)
  have hA : MemBlockL2 (openCubeSet U) A := Lp.memLp A
  have hres : oldSignedEnergyPairing U nu sigma k A R =
      oldSignedEnergyPairing U nu sigma k A G := by
    simpa [A, R, G] using
      (old_signed_residual_cross_pairing U nu sigma hnu hsigma k F G hF hG)
  have hrem := old_signed_mixed_pairing_remainder U nu sigma hnu hsigma k
    hA hF hg
  have hrem' : oldSignedEnergyPairing U nu sigma k A G -
      volumeAverage (openCubeSet U) (fun x => vecDot (F x).2 (g x)) =
      volumeAverage (openCubeSet U) (fun x =>
        vecDot ((scalarCoefficientFlux a A x).2 - (F x).2) (g x)) := by
    simpa [scalarCoefficientFlux, a, A, G] using hrem
  change 2 * (oldSignedEnergyPairing U nu sigma k A R -
      volumeAverage (openCubeSet U) (fun x => vecDot (F x).2 (g x))) =
    -2 * volumeAverage (openCubeSet U) (fun x =>
      vecDot (-g x) ((scalarCoefficientFlux a A x).2 - (F x).2))
  have havg : volumeAverage (openCubeSet U) (fun x =>
      vecDot (-g x) ((scalarCoefficientFlux a A x).2 - (F x).2)) =
      -volumeAverage (openCubeSet U) (fun x =>
        vecDot ((scalarCoefficientFlux a A x).2 - (F x).2) (g x)) := by
    have hfun : (fun x =>
        vecDot (-g x) ((scalarCoefficientFlux a A x).2 - (F x).2)) =
        (-1 : ℝ) • (fun x =>
          vecDot ((scalarCoefficientFlux a A x).2 - (F x).2) (g x)) := by
      funext x
      simp [vecDot_neg_left, vecDot_comm]
    rw [hfun, volumeAverage_smul]
    simp
  rw [hres, hrem', havg]
  ring

/-- Negating the reciprocal receiver negates its signed source carrier. -/
theorem main_e_cell_cross_neg_right (U : TriadicCube 2)
    (f e : Vec 2 → Vec 2) :
    mainECellCrossCarrier U f (-e) = -mainECellCrossCarrier U f e := by
  unfold mainECellCrossCarrier
  have hpoint : (fun x => vecDot (f x) (-e x)) =
      (-1 : ℝ) • (fun x => vecDot (f x) (e x)) := by
    funext x
    simp [vecDot_neg_right]
  change -2 * volumeAverage (openCubeSet U)
      (fun x => vecDot (f x) (-e x)) = _
  rw [hpoint, volumeAverage_smul]
  simp

/-- The actual mixed pairing partitions over the physical cell family as
the source-paired reciprocal defect. `hHpure` records the pure-second
structure of the actual OLD source; no estimate is assumed. -/
theorem main_e_mixed_pairing_cell_partition
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F H : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (hH : MemBlockL2 (openCubeSet Q) H)
    (hHpure : H = fun x => (0, (H x).2)) :
    2 * (oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k H hH) -
      volumeAverage (openCubeSet Q)
        (fun x => vecDot (F x).2 (H x).2)) =
    oldSignedCellAverage Q depth (fun U =>
      mainECellCrossCarrier U
        (fun x => -(H x).2)
        (mainECellTopReciprocalDefect U
          (responseFramePlanarCoefficientField nu sigma
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k F hF)
          F)) := by
  have hpartition := old_signed_mixed_pairing_partition Q depth nu sigma
    hnu hsigma k F H hF hH
  rw [hpartition, ← old_signed_cell_average_mul Q depth 2]
  congr 1
  funext U
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let Fcell : MemBlockL2 (openCubeSet U.val) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hsub)
  let Hcell : MemBlockL2 (openCubeSet U.val) H :=
    hH.mono_measure (Measure.restrict_mono_set volume hsub)
  let G : Vec 2 → BlockVec 2 := fun x => (0, (H x).2)
  let Gcell : MemBlockL2 (openCubeSet U.val) G :=
    memBlockL2_blockField MemLp.zero (memVectorL2_snd_of_memBlockL2 Hcell)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F hF
  let RH := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k H hH
  let RG := scalarResidualField U.val nu sigma hnu hsigma kU
    (toHilbertBlockL2OfBlockField Gcell)
  have hAH := old_signed_residual_cross_pairing U.val nu sigma hnu hsigma kU
    F H Fcell Hcell
  have hAG := old_signed_residual_cross_pairing U.val nu sigma hnu hsigma kU
    F G Fcell Gcell
  have hres : oldSignedEnergyPairing U.val nu sigma kU A RH =
      oldSignedEnergyPairing U.val nu sigma kU A RG := by
    calc
      oldSignedEnergyPairing U.val nu sigma kU A RH =
          oldSignedEnergyPairing U.val nu sigma kU A H := by
            simpa [A, RH, oldSignedCellResidual, hsub, kU] using hAH
      _ = oldSignedEnergyPairing U.val nu sigma kU A G := by
            rw [hHpure]
      _ = oldSignedEnergyPairing U.val nu sigma kU A RG := by
            simpa [A, RG, oldSignedCellResidual, hsub, kU] using hAG.symm
  have hcell := main_e_cell_top_mixed_pairing_identity U.val nu sigma
    hnu hsigma kU F Fcell (fun x => (H x).2)
    (memVectorL2_snd_of_memBlockL2 Hcell)
  calc
    2 * (oldSignedEnergyPairing U.val nu sigma kU A RH -
        volumeAverage (openCubeSet U.val)
          (fun x => vecDot (F x).2 (H x).2)) =
        2 * (oldSignedEnergyPairing U.val nu sigma kU A RG -
          volumeAverage (openCubeSet U.val)
            (fun x => vecDot (F x).2 (H x).2)) := by rw [hres]
    _ = mainECellCrossCarrier U.val (fun x => -(H x).2)
          (mainECellTopReciprocalDefect U.val
            (responseFramePlanarCoefficientField nu sigma kU)
            (scalarResidualField U.val nu sigma hnu hsigma kU
              (toHilbertBlockL2OfBlockField Fcell)) F) := by
        simpa [A, RG, G, oldSignedCellResidual, hsub, kU] using hcell

/-- The bottom mixed pairing has the source convention after reversing the
reciprocal defect. -/
theorem main_e_mixed_pairing_cell_partition_bottom
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F H : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (hH : MemBlockL2 (openCubeSet Q) H)
    (hHpure : H = fun x => (0, (H x).2)) :
    (-2 : ℝ) * (oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k H hH) -
      volumeAverage (openCubeSet Q)
        (fun x => vecDot (F x).2 (H x).2)) =
    oldSignedCellAverage Q depth (fun U =>
      mainECellCrossCarrier U
        (fun x => -(H x).2)
        (mainECellBottomReciprocalDefect U
          (responseFramePlanarCoefficientField nu sigma
            (oldSignedCellCoefficient Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k F hF)
          F)) := by
  have htop := main_e_mixed_pairing_cell_partition Q depth nu sigma
    hnu hsigma k F H hF hH hHpure
  calc
    (-2 : ℝ) * (oldSignedEnergyPairing Q nu sigma k
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k H hH) -
        volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (H x).2)) =
      -(2 * (oldSignedEnergyPairing Q nu sigma k
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF)
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k H hH) -
        volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (H x).2))) := by ring
    _ = -(oldSignedCellAverage Q depth (fun U =>
        mainECellCrossCarrier U
          (fun x => -(H x).2)
          (mainECellTopReciprocalDefect U
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF)
            F))) := congrArg Neg.neg htop
    _ = oldSignedCellAverage Q depth (fun U =>
        mainECellCrossCarrier U
          (fun x => -(H x).2)
          (mainECellBottomReciprocalDefect U
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF)
            F)) := by
      let topC := fun U : OldSignedCellIndex Q depth =>
        mainECellCrossCarrier U.val (fun x => -(H x).2)
          (mainECellTopReciprocalDefect U.val
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF) F)
      let bottomC := fun U : OldSignedCellIndex Q depth =>
        mainECellCrossCarrier U.val (fun x => -(H x).2)
          (mainECellBottomReciprocalDefect U.val
            (responseFramePlanarCoefficientField nu sigma
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF) F)
      have hneg (U : OldSignedCellIndex Q depth) : bottomC U = -topC U := by
        dsimp [topC, bottomC]
        change mainECellCrossCarrier U.val (fun x => -(H x).2)
            (fun x => -((scalarCoefficientFlux
              (responseFramePlanarCoefficientField nu sigma
                (oldSignedCellCoefficient Q U.val
                  (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
              (oldSignedCellResidual Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
                nu sigma hnu hsigma k F hF) x).2 - (F x).2)) =
          -mainECellCrossCarrier U.val (fun x => -(H x).2)
            (fun x => (scalarCoefficientFlux
              (responseFramePlanarCoefficientField nu sigma
                (oldSignedCellCoefficient Q U.val
                  (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
              (oldSignedCellResidual Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
                nu sigma hnu hsigma k F hF) x).2 - (F x).2)
        exact main_e_cell_cross_neg_right U.val (fun x => -(H x).2) _
      calc
        -oldSignedCellAverage Q depth topC =
            (-1 : ℝ) * oldSignedCellAverage Q depth topC := by ring
        _ = oldSignedCellAverage Q depth (fun U => (-1 : ℝ) * topC U) :=
            (old_signed_cell_average_mul Q depth (-1) topC).symm
        _ = oldSignedCellAverage Q depth bottomC := by
            congr 1
            funext U
            rw [hneg U]
            ring

end
end ASDExplicitGamma.Main

end
