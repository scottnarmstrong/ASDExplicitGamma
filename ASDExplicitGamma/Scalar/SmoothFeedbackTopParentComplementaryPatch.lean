module

public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Native.OldSignedEnergyPartition
public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra
public import ASDExplicitGamma.Variational.PairedBessel

/-! The source top-parent complementary/reflected patch identity for the actual
OLD coefficient. The parent uses the actual affine-top response and the
descendant patch uses actual bottom-affine local residuals. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3

noncomputable section

/-- The energy of the actual finite bottom-affine patch is the average of its
descendant coarse lower-right quadratics. -/
private theorem top_parent_complementary_patch_cell_energy_identity
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P))
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)) =
    descendantsAverage Q depth (fun R =>
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField nu sigma k)) P)) := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const P
  let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  have hLenergy := old_signed_local_residual_energy Q depth nu sigma hnu hsigma k
    F F hF hF
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) :
      volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x)
          (blockMatVecMul (blockCoeffField a x) (L x))) =
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P) := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField nu sigma kR
    let hFR : MemBlockL2 (openCubeSet R) F :=
      hF.mono_measure (Measure.restrict_mono_set volume hRQ)
    let Z : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ
      nu sigma hnu hsigma k F hF
    have hRestr := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
      F hF R hR
    have hCoeffMat (x : Vec 2) (hx : x ∈ openCubeSet R) : aR x = a x := by
      simp only [aR, a, responseFramePlanarCoefficientField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hCoeff (x : Vec 2) (hx : x ∈ openCubeSet R) :
        blockCoeffField aR x = blockCoeffField a x := by
      simpa [blockCoeffField] using congrArg blockMatrixOfCoeff (hCoeffMat x hx)
    have hCoeffAE : aR =ᵐ[volume.restrict (openCubeSet R)] a := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      exact hCoeffMat x hx
    have hCoarse := coarseBlockMatrix_congr_of_ae_eq hCoeffAE
    have hRestr' : L =ᵐ[volumeMeasureOn (openCubeSet R)] Z := by
      simpa [L, Z] using hRestr
    have hIntegrand : (fun x => blockVecDot (L x)
        (blockMatVecMul (blockCoeffField a x) (L x))) =ᵐ[
          volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot (Z x)
          (blockMatVecMul (blockCoeffField aR x) (Z x))) := by
      filter_upwards [hRestr', ae_restrict_mem (measurableSet_openCubeSet R)]
        with x hLx hx
      rw [hLx, hCoeff x hx]
    have hAverage : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x)
          (blockMatVecMul (blockCoeffField a x) (L x))) =
        volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (Z x)
            (blockMatVecMul (blockCoeffField aR x) (Z x))) := by
      unfold volumeAverage
      congr 1
      exact integral_congr_ae hIntegrand
    have hFRconst : toHilbertBlockL2OfBlockField hFR =
        (scalarFrameRealization R nu sigma hnu hsigma kR).constantField P := by
      have hconst : toHilbertBlockL2OfBlockField hFR =
          blockVecToHilbertBlockL2Const P := by
        apply Lp.ext
        filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFR,
          coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet R) P] with x hx hy
        simpa [F] using hx.trans hy.symm
      exact hconst.trans (by rfl)
    have hZeq : Z = scalarResidualField R nu sigma hnu hsigma kR
        ((scalarFrameRealization R nu sigma hnu hsigma kR).constantField P) := by
      funext x
      change (scalarResidualField R nu sigma hnu hsigma kR
        (toHilbertBlockL2OfBlockField hFR)) x = _
      rw [hFRconst]
    have hAffine := old_signed_affine_energy R nu sigma hnu hsigma kR P
    have hAffineZ : oldSignedEnergyPairing R nu sigma kR Z Z =
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) := by
      simpa [hZeq, aR] using hAffine
    calc
      _ = oldSignedEnergyPairing R nu sigma kR Z Z := by
        simpa [oldSignedEnergyPairing, aR] using hAverage
      _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) := hAffineZ
      _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P) := by rw [hCoarse]
  rw [hLenergy]
  unfold descendantsAverage
  change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q depth, volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x) (blockMatVecMul (blockCoeffField a x) (L x))) =
    ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q depth,
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P)
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  exact hcell R hR

/-- The reflected cross term between the actual top-affine parent minimizer
and the actual bottom-affine finite patch is the squared affine load. -/
private theorem top_parent_complementary_reflected_cross
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (S T : Vec 2 → BlockVec 2)
    (hSmem : MemBlockL2 (openCubeSet Q) S)
    (hTmem : MemBlockL2 (openCubeSet Q) T)
    (hSvar : ScalarVariation (openCubeSet Q)
      (fun x => S x - ((e, 0) : BlockVec 2)))
    (hTvar : ScalarVariation (openCubeSet Q)
      (fun x => T x - ((0, e) : BlockVec 2))) :
    oldSignedEnergyPairing Q nu sigma k S
      (fun x => (pairedReflectState
        (responseFramePlanarCoefficientField nu sigma k)
        ⟨fun x => (T x).1, fun x => (T x).2⟩).eval x) = vecNormSq e := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
  let J : Vec 2 → BlockVec 2 := (pairedReflectState a Tstate).eval
  let Z : Vec 2 → BlockVec 2 := fun x => T x - Pbot
  have hScompatible : ScalarCompatible U S := by
    have hCorr := scalar_variation_compatible hSvar
    have hSfirst : IsPotentialOn U (fun x => (S x).1) := by
      have hConstPot : IsPotentialOn U (fun _ : Vec 2 => e) :=
        (H1Function.affineOnIsSobolevRegularDomain
          (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain e).isPotentialOn
      have hsum := isPotentialOn_add
        (by simpa [Ptop] using hCorr.2.1) hConstPot
      have hfields : (fun x => ((S x).1 - e) + e) = (fun x => (S x).1) := by
        funext x
        exact sub_add_cancel _ _
      exact hfields ▸ hsum
    have hSsecond : IsSolenoidalOn U (fun x => (S x).2) := by
      simpa [Ptop] using hCorr.2.2
    exact ⟨hSmem, hSfirst, hSsecond⟩
  have hJmem : MemBlockL2 U J := by
    have hImage := scalar_coefficient_flux_memL2 Q a hEll hTmem
    have hImageFst : MemVectorL2 U (fun x => (scalarCoefficientFlux a T x).1) :=
      memVectorL2_fst_of_memBlockL2 hImage
    have hImageSnd : MemVectorL2 U (fun x => (scalarCoefficientFlux a T x).2) :=
      memVectorL2_snd_of_memBlockL2 hImage
    change MemBlockL2 U (fun x => ((scalarCoefficientFlux a T x).2,
      (scalarCoefficientFlux a T x).1))
    exact memBlockL2_blockField hImageSnd hImageFst
  have hAction : (fun x => scalarCoefficientFlux a J x) =ᵐ[volumeMeasureOn U]
      (fun x => (T x).swap) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    change blockMatVecMul (blockCoeffField a x) ((pairedReflectState a Tstate).eval x) = _
    exact pairedReflectState_action hEll Tstate hx
  have hCrossPoint :
      (fun x => blockVecDot (S x) (scalarCoefficientFlux a J x)) =ᵐ[
        volumeMeasureOn U]
      (fun x => blockVecDot (scalarBlockExchange (S x)) (T x)) := by
    filter_upwards [hAction] with x hx
    rw [hx]
    simp [scalarBlockExchange, blockVecDot, vecDot]
    ring
  have hSdeltaMean : volumeAverageVec U (fun x => (S x).1 - e) = 0 := by
    funext i
    apply volumeAverage_eq_zero_of_integral_eq_zero
    have hz := IsPotentialZeroTraceOn.integral_eq_zero (by
      simpa [Ptop] using hSvar.2.1)
    exact congrFun hz i
  have hSfirstMean : volumeAverageVec U (fun x => (S x).1) = e := by
    funext i
    have hcoord : IntegrableOn (fun x => ((S x).1 - e) i) U :=
      CorrectionFieldData.integrableOn_coord_of_memVectorL2
        (by simpa [Ptop] using memVectorL2_fst_of_memBlockL2 hSvar.1) i
    have hconst : IntegrableOn (fun _ : Vec 2 => e i) U :=
      CorrectionFieldData.integrableOn_coord_of_memVectorL2 (memLp_const e) i
    change volumeAverage U (fun x => (S x).1 i) = e i
    calc
      volumeAverage U (fun x => (S x).1 i) =
          volumeAverage U (fun x => ((S x).1 - e) i + e i) := by
        congr 1
        funext x
        exact (sub_add_cancel _ _).symm
      _ = volumeAverage U (fun x => ((S x).1 - e) i) +
          volumeAverage U (fun _ : Vec 2 => e i) := volumeAverage_add hcoord hconst
      _ = e i := by
        rw [show volumeAverage U (fun x => ((S x).1 - e) i) = 0 from
          congrFun hSdeltaMean i]
        simp [volumeAverage_const,
          show (volume U).toReal ≠ 0 by
            rw [volume_openCubeSet_toReal]
            exact (cubeVolume_pos Q).ne']
  have hCrossConst : volumeAverage U
      (fun x => blockVecDot (scalarBlockExchange (S x)) Pbot) = vecNormSq e := by
    have hcoord : ∀ i, IntegrableOn (fun x => (S x).1 i) U := by
      intro i
      exact CorrectionFieldData.integrableOn_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2 hSmem) i
    calc
      volumeAverage U (fun x => blockVecDot (scalarBlockExchange (S x)) Pbot) =
          vecDot (volumeAverageVec U (fun x => (S x).1)) e := by
        rw [show (fun x => blockVecDot (scalarBlockExchange (S x)) Pbot) =
          (fun x => vecDot (S x).1 e) by
            funext x
            simp [scalarBlockExchange, Pbot, blockVecDot, vecDot]]
        exact volumeAverage_vecDot_right (fun x => (S x).1) e hcoord
      _ = vecNormSq e := by rw [hSfirstMean]; rfl
  have hCrossVariationInt : IntegrableOn
      (fun x => blockVecDot (scalarBlockExchange (S x)) (Z x)) U := by
    have h1 := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_snd_of_memBlockL2 hSmem)
      (memVectorL2_fst_of_memBlockL2 hTvar.1)
    have h2 := integrableOn_vecDot_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 hSmem)
      (memVectorL2_snd_of_memBlockL2 hTvar.1)
    change IntegrableOn (fun x => vecDot (S x).2 (Z x).1 +
      vecDot (S x).1 (Z x).2) U
    exact h1.add h2
  have hCrossConstInt : IntegrableOn
      (fun x => blockVecDot (scalarBlockExchange (S x)) Pbot) U := by
    have heq : (fun x => blockVecDot (scalarBlockExchange (S x)) Pbot) =
        (fun x => vecDot (S x).1 e) := by
      funext x
      simp [scalarBlockExchange, Pbot, blockVecDot, vecDot]
    rw [heq]
    exact integrableOn_vecDot_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 hSmem) (memLp_const e)
  have hCrossVariationZero : volumeAverage U
      (fun x => blockVecDot (scalarBlockExchange (S x)) (Z x)) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero
      (by simpa [Z, Pbot] using
        scalar_compatible_exchange_pairing_zero hScompatible hTvar)
  have hCrossSplit : volumeAverage U
      (fun x => blockVecDot (scalarBlockExchange (S x)) (T x)) =
      volumeAverage U (fun x => blockVecDot (scalarBlockExchange (S x)) Pbot) +
        volumeAverage U (fun x => blockVecDot (scalarBlockExchange (S x)) (Z x)) := by
    calc
      _ = volumeAverage U (fun x => blockVecDot (scalarBlockExchange (S x))
          (Pbot + Z x)) := by
        congr 1
        funext x
        exact congrArg (fun V : BlockVec 2 =>
          blockVecDot (scalarBlockExchange (S x)) V)
          (by simp [Z, Pbot])
      _ = _ := by
        have heq : (fun x => blockVecDot (scalarBlockExchange (S x))
            (Pbot + Z x)) = (fun x =>
              blockVecDot (scalarBlockExchange (S x)) Pbot +
                blockVecDot (scalarBlockExchange (S x)) (Z x)) := by
          funext x
          exact blockVecDot_add_right _ _ _
        rw [heq]
        exact volumeAverage_add hCrossConstInt hCrossVariationInt
  have hCross : oldSignedEnergyPairing Q nu sigma k S J = vecNormSq e := by
    calc
      oldSignedEnergyPairing Q nu sigma k S J =
          volumeAverage U (fun x =>
            blockVecDot (scalarBlockExchange (S x)) (T x)) := by
        change volumeAverage U (fun x =>
          blockVecDot (S x) (scalarCoefficientFlux a J x)) = _
        unfold volumeAverage
        congr 1
        exact integral_congr_ae hCrossPoint
      _ = vecNormSq e := by
        rw [hCrossSplit, hCrossConst, hCrossVariationZero]
        simp
  exact hCross

/-- The top-parent complementary patch identity for the actual OLD
coefficient. The parent is the recovered affine-top minimizer; the children
are the actual bottom-affine `oldSignedLocalResidual` patches. -/
theorem smooth_feedback_top_parent_complementary_patch_identity
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    let k := oldCutoffSkewCoefficient m Q ω
    let a := responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M m : ℝ) k
    let Ptop : BlockVec 2 := (e, 0)
    let Pbot : BlockVec 2 := (0, e)
    let S : Vec 2 → BlockVec 2 :=
      smoothFeedbackCellAffineResidual M m Q e ω
    let T : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).property k
      (fun _ => Pbot) (memLp_const Pbot)
    let J : Vec 2 → BlockVec 2 := (pairedReflectState a
      ⟨fun x => (T x).1, fun x => (T x).2⟩).eval
    oldSignedEnergyPairing Q M.nu (Annealed.sigmaBar M m : ℝ) k
      (fun x => S x - J x) (fun x => S x - J x) =
      blockVecDot Ptop (blockMatVecMul
        (coarseBlockMatrix (openCubeSet Q) a) Ptop) +
        descendantsAverage Q depth (fun R =>
          blockVecDot Pbot (blockMatVecMul
            (coarseBlockMatrix (openCubeSet R) a) Pbot)) - 2 * vecNormSq e := by
  classical
  dsimp only
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let S : Vec 2 → BlockVec 2 := smoothFeedbackCellAffineResidual M m Q e ω
  let F : Vec 2 → BlockVec 2 := fun _ => Pbot
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const Pbot
  let T : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k F hF
  let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
  let J : Vec 2 → BlockVec 2 := (pairedReflectState a Tstate).eval
  let Z : Vec 2 → BlockVec 2 := fun x => S x - J x
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).property k
  have hSmem : MemBlockL2 (openCubeSet Q) S := by
    simpa [S, smoothFeedbackCellAffineResidual] using
      scalar_cell_response_test_memL2 Q a hEll Ptop
  have hTmem : MemBlockL2 (openCubeSet Q) T :=
    old_signed_local_residual_memLp Q depth M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k F hF
  have hSvar : ScalarVariation (openCubeSet Q) (fun x => S x - Ptop) := by
    simpa [S, Ptop, smoothFeedbackCellAffineResidual, a, hEll] using
      scalar_cell_response_test_variation Q a hEll Ptop
  have hTvar : ScalarVariation (openCubeSet Q) (fun x => T x - Pbot) := by
    have hremoved := old_signed_local_removed_variation Q depth M.nu σ
      M.nu_pos (Annealed.sigmaBar M m).property k F hF
    have hscaled := scalar_variation_smul hremoved (-1 : ℝ)
    have hfields : (fun x => (-1 : ℝ) •
        (F x - oldSignedLocalResidual Q depth M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).property k F hF x)) =
        (fun x => T x - Pbot) := by
      funext x
      ext i <;> simp [F, T, Pbot, sub_eq_add_neg, smul_eq_mul] <;> ring
    change ScalarVariation (openCubeSet Q) (fun x => (-1 : ℝ) •
      (F x - oldSignedLocalResidual Q depth M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k F hF x)) at hscaled
    rw [hfields] at hscaled
    exact hscaled
  have hSenergy : oldSignedEnergyPairing Q M.nu σ k S S =
      blockVecDot Ptop (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) Ptop) := by
    have hProj := smooth_feedback_affine_projection_ae M m Q e ω
    have hPair := old_signed_energy_pairing_congr_ae Q M.nu σ k hProj hProj
    have hAffine := old_signed_affine_energy Q M.nu σ
      M.nu_pos (Annealed.sigmaBar M m).property k Ptop
    exact hPair.symm.trans hAffine
  have hTenergy := top_parent_complementary_patch_cell_energy_identity
    Q depth M.nu σ M.nu_pos (Annealed.sigmaBar M m).property k Pbot
  have hCross := top_parent_complementary_reflected_cross Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k e S T hSmem hTmem hSvar hTvar
  have hJmem : MemBlockL2 (openCubeSet Q) J := by
    have hImage := scalar_coefficient_flux_memL2 Q a hEll hTmem
    change MemBlockL2 (openCubeSet Q)
      (fun x => ((scalarCoefficientFlux a T x).2, (scalarCoefficientFlux a T x).1))
    exact memBlockL2_blockField (memVectorL2_snd_of_memBlockL2 hImage)
      (memVectorL2_fst_of_memBlockL2 hImage)
  have hZmem : MemBlockL2 (openCubeSet Q) Z := hSmem.sub hJmem
  have hExpand := old_signed_energy_pairing_sub_left Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k hSmem hJmem hZmem
  have hExpandS := old_signed_energy_pairing_sub_right Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k hSmem hSmem hJmem
  have hExpandJ := old_signed_energy_pairing_sub_right Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k hJmem hSmem hJmem
  have hJenergy : oldSignedEnergyPairing Q M.nu σ k J J =
      oldSignedEnergyPairing Q M.nu σ k T T := by
    change blockPairingAverage (openCubeSet Q) a
      (pairedReflectState a Tstate) (pairedReflectState a Tstate) =
      blockPairingAverage (openCubeSet Q) a Tstate Tstate
    exact pairedReflect_pairingAverage_isometry hEll Tstate Tstate
  have hD4 : oldSignedEnergyPairing Q M.nu σ k Z Z =
      oldSignedEnergyPairing Q M.nu σ k S S +
        oldSignedEnergyPairing Q M.nu σ k T T - 2 * vecNormSq e := by
    have hZeq : Z = S - J := by
      funext x
      rfl
    have hExpandZ : oldSignedEnergyPairing Q M.nu σ k Z Z =
        oldSignedEnergyPairing Q M.nu σ k S Z -
          oldSignedEnergyPairing Q M.nu σ k J Z := by
      rw [hZeq]
      exact hExpand
    have hExpandSZ : oldSignedEnergyPairing Q M.nu σ k S Z =
        oldSignedEnergyPairing Q M.nu σ k S S -
          oldSignedEnergyPairing Q M.nu σ k S J := by
      rw [hZeq]
      exact hExpandS
    have hExpandJZ : oldSignedEnergyPairing Q M.nu σ k J Z =
        oldSignedEnergyPairing Q M.nu σ k J S -
          oldSignedEnergyPairing Q M.nu σ k J J := by
      rw [hZeq]
      exact hExpandJ
    calc
      oldSignedEnergyPairing Q M.nu σ k Z Z =
          oldSignedEnergyPairing Q M.nu σ k S Z -
            oldSignedEnergyPairing Q M.nu σ k J Z := hExpandZ
      _ = (oldSignedEnergyPairing Q M.nu σ k S S -
            oldSignedEnergyPairing Q M.nu σ k S J) -
          (oldSignedEnergyPairing Q M.nu σ k J S -
            oldSignedEnergyPairing Q M.nu σ k J J) := by
        rw [hExpandSZ, hExpandJZ]
      _ = oldSignedEnergyPairing Q M.nu σ k S S +
          oldSignedEnergyPairing Q M.nu σ k T T - 2 * vecNormSq e := by
        rw [old_signed_energy_pairing_symm Q M.nu σ k J S,
          hJenergy, hCross]
        ring
  calc
    oldSignedEnergyPairing Q M.nu σ k Z Z =
        oldSignedEnergyPairing Q M.nu σ k S S +
          oldSignedEnergyPairing Q M.nu σ k T T - 2 * vecNormSq e := hD4
    _ = blockVecDot Ptop (blockMatVecMul
          (coarseBlockMatrix (openCubeSet Q) a) Ptop) +
        descendantsAverage Q depth (fun R =>
          blockVecDot Pbot (blockMatVecMul
            (coarseBlockMatrix (openCubeSet R) a) Pbot)) - 2 * vecNormSq e := by
      rw [hSenergy, hTenergy]

end
end ASDExplicitGamma.Scalar
