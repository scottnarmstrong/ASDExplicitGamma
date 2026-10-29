module

public import ASDExplicitGamma.Main.HotCovCarrier
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Scalar.CoefficientFlux
public import ASDExplicitGamma.Main.HotPatchTrial
public import ASDExplicitGamma.Main.ETermMixedCarrier

/-! MA-E-COVARIANCE: the hot trial's mixed cross is exactly the affine carrier plus the
oscillatory carrier, cell by cell and mode by mode. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational ASDExplicitGamma.Inverse

noncomputable section

/-- Oscillatory top contribution, the exact remainder after removing the
actual cell-mean affine receiver. -/
noncomputable def hotCovTopOscCross
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (i : Fin 2) (U : OldSignedCellIndex Q depth) : ℝ :=
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let F := oldSignedFlatInput Q b L true n i
  let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
    (oldSignedFlatLoad true i)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F
    (old_signed_flat_input_memL2 Q b L true n i)
  let eaff := mainECellTopAffineOfFlatInput U.val a hEll F
  mainECellCrossCarrier U.val (fun x => -(H x).2)
    (mainECellTopOscillatoryReceiver U.val a A F eaff)

/-- Oscillatory bottom contribution, the exact remainder after removing the
actual cell-mean affine receiver. -/
noncomputable def hotCovBotOscCross
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (i : Fin 2) (U : OldSignedCellIndex Q depth) : ℝ :=
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let F := oldSignedFlatInput Q b L false n i
  let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
    (oldSignedFlatLoad false i)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F
    (old_signed_flat_input_memL2 Q b L false n i)
  let eaff := mainECellBottomAffineOfFlatInput U.val a hEll F
  mainECellCrossCarrier U.val (fun x => -(H x).2)
    (mainECellBottomOscillatoryReceiver U.val a A F eaff)

/-- The actual top source and both receivers are integrable on each cell.
The proof uses L2 membership of the localized source, coefficient flux,
and canonical affine minimizer. -/
theorem hotCov_top_cell_cross_split
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (i : Fin 2) (U : OldSignedCellIndex Q depth) :
    mainECellCrossCarrier U.val
      (fun x => -(hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
        (oldSignedFlatLoad true i) x).2)
      (mainECellTopReciprocalDefect U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (oldSignedFlatInput Q b L true n i)
          (old_signed_flat_input_memL2 Q b L true n i))
        (oldSignedFlatInput Q b L true n i)) =
      hotCovTopAffCross Q depth nu sigma hnu hsigma k b L n i U +
      hotCovTopOscCross Q depth nu sigma hnu hsigma k b L n i U := by
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let F := oldSignedFlatInput Q b L true n i
  let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
    (oldSignedFlatLoad true i)
  let hFparent := old_signed_flat_input_memL2 Q b L true n i
  let hF : MemBlockL2 (openCubeSet U.val) F :=
    hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let hHparent := hot_patch_source_memL2 Q depth depth nu sigma
    hnu hsigma k b L n (oldSignedFlatLoad true i)
  let hH : MemBlockL2 (openCubeSet U.val) H :=
    hHparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F hFparent
  let eaff := mainECellTopAffineOfFlatInput U.val a hEll F
  let e := mainECellTopReciprocalDefect U.val a A F
  let f := fun x => -(H x).2
  have hf : MemVectorL2 (openCubeSet U.val) f :=
    (memVectorL2_snd_of_memBlockL2 hH).neg
  have hA : MemBlockL2 (openCubeSet U.val) A := A.property
  have hflux := memVectorL2_snd_of_memBlockL2
    (scalar_coefficient_flux_memL2 U.val a hEll hA)
  have hF2 := memVectorL2_snd_of_memBlockL2 hF
  have he : MemVectorL2 (openCubeSet U.val) e := by
    change MemVectorL2 (openCubeSet U.val)
      (fun x => (scalarCoefficientFlux a A x).2 - (F x).2)
    exact hflux.sub hF2
  let C := oldSignedCanonicalAffineField U.val a hEll
    (0, -(oldSignedBlockMean U.val F).2)
  have hC : MemBlockL2 (openCubeSet U.val) C := Lp.memLp C
  have hCflux := scalar_coefficient_flux_memL2 U.val a hEll hC
  have hC2 := memVectorL2_snd_of_memBlockL2 hCflux
  have hm : MemVectorL2 (openCubeSet U.val)
      (fun _ => -(oldSignedBlockMean U.val F).2) := memLp_const _
  have heaff : MemVectorL2 (openCubeSet U.val) eaff := by
    change MemVectorL2 (openCubeSet U.val)
      (fun x => -((scalarCoefficientFlux a C x).2 -
        (-(oldSignedBlockMean U.val F).2)))
    exact (hC2.sub hm).neg
  have heosc : MemVectorL2 (openCubeSet U.val) (e - eaff) := he.sub heaff
  have hAffInt := integrableOn_vecDot_of_memVectorL2 hf heaff
  have hOscInt := integrableOn_vecDot_of_memVectorL2 hf heosc
  rw [hotCovTopAffCross_eq]
  change mainECellCrossCarrier U.val f e =
    mainECellCrossCarrier U.val f eaff +
      mainECellCrossCarrier U.val f (e - eaff)
  exact main_e_cell_cross_affine_oscillatory_split U.val f e eaff hAffInt hOscInt

/-- The actual bottom source and both receivers are integrable on each cell.
The proof uses L2 membership of the localized source, coefficient flux,
and canonical affine minimizer. -/
theorem hotCov_bot_cell_cross_split
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (i : Fin 2) (U : OldSignedCellIndex Q depth) :
    mainECellCrossCarrier U.val
      (fun x => -(hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
        (oldSignedFlatLoad false i) x).2)
      (mainECellBottomReciprocalDefect U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (oldSignedFlatInput Q b L false n i)
          (old_signed_flat_input_memL2 Q b L false n i))
        (oldSignedFlatInput Q b L false n i)) =
      hotCovBotAffCross Q depth nu sigma hnu hsigma k b L n i U +
      hotCovBotOscCross Q depth nu sigma hnu hsigma k b L n i U := by
  let hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  let kU := oldSignedCellCoefficient Q U.val hsub k
  let a := responseFramePlanarCoefficientField nu sigma kU
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U.val) nu sigma hnu hsigma kU
  let F := oldSignedFlatInput Q b L false n i
  let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
    (oldSignedFlatLoad false i)
  let hFparent := old_signed_flat_input_memL2 Q b L false n i
  let hF : MemBlockL2 (openCubeSet U.val) F :=
    hFparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let hHparent := hot_patch_source_memL2 Q depth depth nu sigma
    hnu hsigma k b L n (oldSignedFlatLoad false i)
  let hH : MemBlockL2 (openCubeSet U.val) H :=
    hHparent.mono_measure (Measure.restrict_mono_set volume hsub)
  let A := oldSignedCellResidual Q U.val hsub nu sigma hnu hsigma k F hFparent
  let eaff := mainECellBottomAffineOfFlatInput U.val a hEll F
  let e := mainECellBottomReciprocalDefect U.val a A F
  let f := fun x => -(H x).2
  have hf : MemVectorL2 (openCubeSet U.val) f :=
    (memVectorL2_snd_of_memBlockL2 hH).neg
  have hA : MemBlockL2 (openCubeSet U.val) A := A.property
  have hflux := memVectorL2_snd_of_memBlockL2
    (scalar_coefficient_flux_memL2 U.val a hEll hA)
  have hF2 := memVectorL2_snd_of_memBlockL2 hF
  have he : MemVectorL2 (openCubeSet U.val) e := by
    change MemVectorL2 (openCubeSet U.val)
      (fun x => -((scalarCoefficientFlux a A x).2 - (F x).2))
    exact (hflux.sub hF2).neg
  let C := oldSignedCanonicalAffineField U.val a hEll
    ((oldSignedBlockMean U.val F).1, 0)
  have hC : MemBlockL2 (openCubeSet U.val) C := Lp.memLp C
  have hCflux := scalar_coefficient_flux_memL2 U.val a hEll hC
  have hC2 := memVectorL2_snd_of_memBlockL2 hCflux
  have heaff : MemVectorL2 (openCubeSet U.val) eaff := by
    change MemVectorL2 (openCubeSet U.val)
      (fun x => -(scalarCoefficientFlux a C x).2)
    exact hC2.neg
  have heosc : MemVectorL2 (openCubeSet U.val) (e - eaff) := he.sub heaff
  have hAffInt := integrableOn_vecDot_of_memVectorL2 hf heaff
  have hOscInt := integrableOn_vecDot_of_memVectorL2 hf heosc
  rw [hotCovBotAffCross_eq]
  change mainECellCrossCarrier U.val f e =
    mainECellCrossCarrier U.val f eaff +
      mainECellCrossCarrier U.val f (e - eaff)
  exact main_e_cell_cross_affine_oscillatory_split U.val f e eaff hAffInt hOscInt


/-- Exact per-mode, per-cell source-row decomposition of the complete
`2*mixedPlus - 2*mixedMinus` group in the actual OLD trial. -/
noncomputable def hotCovMixedModeCarrier
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (U : OldSignedCellIndex Q depth) : ℝ :=
  (∑ i : Fin 2,
    let F := oldSignedFlatInput Q b L true n i
    let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
      (oldSignedFlatLoad true i)
    mainECellCrossCarrier U.val (fun x => -(H x).2)
      (mainECellTopReciprocalDefect U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k F (old_signed_flat_input_memL2 Q b L true n i))
        F)) +
  ∑ i : Fin 2,
    let F := oldSignedFlatInput Q b L false n i
    let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n
      (oldSignedFlatLoad false i)
    mainECellCrossCarrier U.val (fun x => -(H x).2)
      (mainECellBottomReciprocalDefect U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k F (old_signed_flat_input_memL2 Q b L false n i))
        F)

/-- The native mixed group is exactly the normalized depth-cell average of
the actual source paired with its top and bottom reciprocal defects. -/
theorem hotCov_trial_mixed_mode_cell_identity
    (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    let T := hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L
    2 * T.mixedPlus n - 2 * T.mixedMinus n =
      oldSignedCellAverage Q depth
        (hotCovMixedModeCarrier Q depth nu sigma hnu hsigma k b L n) := by
  dsimp only
  let Fp := fun i : Fin 2 => oldSignedFlatInput Q b L true n i
  let Hp := fun i : Fin 2 => hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad true i)
  let Fm := fun i : Fin 2 => oldSignedFlatInput Q b L false n i
  let Hm := fun i : Fin 2 => hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (oldSignedFlatLoad false i)
  let dp := fun i : Fin 2 => oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (Fp i)
        (old_signed_flat_input_memL2 Q b L true n i))
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (Hp i)
        (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n
          (oldSignedFlatLoad true i))) -
    volumeAverage (openCubeSet Q) (fun x => vecDot (Fp i x).2 (Hp i x).2)
  let dm := fun i : Fin 2 => oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (Fm i)
        (old_signed_flat_input_memL2 Q b L false n i))
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (Hm i)
        (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n
          (oldSignedFlatLoad false i))) -
    volumeAverage (openCubeSet Q) (fun x => vecDot (Fm i x).2 (Hm i x).2)
  let cp := fun i : Fin 2 => fun U : OldSignedCellIndex Q depth =>
    mainECellCrossCarrier U.val (fun x => -(Hp i x).2)
      (mainECellTopReciprocalDefect U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (Fp i)
          (old_signed_flat_input_memL2 Q b L true n i))
        (Fp i))
  let cm := fun i : Fin 2 => fun U : OldSignedCellIndex Q depth =>
    mainECellCrossCarrier U.val (fun x => -(Hm i x).2)
      (mainECellBottomReciprocalDefect U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (Fm i)
          (old_signed_flat_input_memL2 Q b L false n i))
        (Fm i))
  have hpure (i : Fin 2) : Hp i = fun x => (0, (Hp i x).2) := by
    funext x
    simp [Hp, hotPatchSource, oldSignedLocalizedPotentialShear]
  have mp (i : Fin 2) : 2 * dp i = oldSignedCellAverage Q depth (cp i) := by
    exact main_e_mixed_pairing_cell_partition Q depth nu sigma hnu hsigma k
      (Fp i) (Hp i) (old_signed_flat_input_memL2 Q b L true n i)
      (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n
        (oldSignedFlatLoad true i)) (hpure i)
  have mm (i : Fin 2) : (-2 : ℝ) * dm i = oldSignedCellAverage Q depth (cm i) := by
    exact main_e_mixed_pairing_cell_partition_bottom Q depth nu sigma hnu hsigma k
      (Fm i) (Hm i) (old_signed_flat_input_memL2 Q b L false n i)
      (hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n
        (oldSignedFlatLoad false i)) (by
          funext x
          simp [Hm, hotPatchSource, oldSignedLocalizedPotentialShear])
  have hTplus : (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).mixedPlus n =
      ∑ i : Fin 2, dp i := by
    rfl
  have hTminus : (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).mixedMinus n =
      ∑ i : Fin 2, dm i := by
    rfl
  rw [hTplus, hTminus]
  have hsum : 2 * (∑ i : Fin 2, dp i) - 2 * (∑ i : Fin 2, dm i) =
      ∑ i : Fin 2, (2 * dp i + (-2) * dm i) := by
    simp only [Finset.mul_sum]
    simp only [sub_eq_add_neg]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    congr 1
    funext i
    ring
  rw [hsum]
  simp_rw [mp, mm]
  rw [Finset.sum_add_distrib]
  rw [← old_signed_cell_average_sum Q depth Finset.univ cp]
  rw [← old_signed_cell_average_sum Q depth Finset.univ cm]
  exact (old_signed_cell_average_add Q depth
    (fun U => ∑ i : Fin 2, cp i U)
    (fun U => ∑ i : Fin 2, cm i U)).symm


/-- Modewise oscillatory carrier of the hot trial (the part of the mixed cross that belongs to
MA-E-OSCILLATION). -/
def hotCovOscMode (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (U : OldSignedCellIndex Q d) : ℝ :=
  (∑ i : Fin 2, hotCovTopOscCross Q d nu sigma hnu hsigma k b L n i U) +
    ∑ i : Fin 2, hotCovBotOscCross Q d nu sigma hnu hsigma k b L n i U

theorem hotCov_mixed_carrier_split (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (U : OldSignedCellIndex Q d) :
    hotCovMixedModeCarrier Q d nu sigma hnu hsigma k b L n U =
      hotCovAffMode Q d nu sigma hnu hsigma k b L n U +
        hotCovOscMode Q d nu sigma hnu hsigma k b L n U := by
  simp only [hotCovMixedModeCarrier, hotCovAffMode, hotCovOscMode]
  simp_rw [hotCov_top_cell_cross_split, hotCov_bot_cell_cross_split]
  simp only [Finset.sum_add_distrib]
  ring

/-- THE IDENTIFICATION: every mode of the hot trial's mixed cross is the affine carrier plus the
oscillatory carrier, equal-volume cell-averaged. -/
theorem hotCov_trial_mixed_split (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) :
    let T := hotPatchTrialTerms Q d nu sigma hnu hsigma k b L
    2 * T.mixedPlus n - 2 * T.mixedMinus n =
      oldSignedCellAverage Q d (hotCovAffMode Q d nu sigma hnu hsigma k b L n) +
      oldSignedCellAverage Q d (hotCovOscMode Q d nu sigma hnu hsigma k b L n) := by
  intro T
  rw [hotCov_trial_mixed_mode_cell_identity Q d nu sigma hnu hsigma k b L n,
    ← old_signed_cell_average_add]
  congr 1
  funext U
  exact hotCov_mixed_carrier_split Q d nu sigma hnu hsigma k b L n U

end

end ASDExplicitGamma.Main
