module

public import ASDExplicitGamma.Main.EnvelopeXIActual
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit

/-! Local depth-five OLD parent-gap carriers for MA-MIXED-BRIDGE. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Cold ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

noncomputable local instance mixedBridgeLocalBlockL2Measurable
    (U : TriadicCube 2) : MeasurableSpace (BlockL2 (openCubeSet U)) := borel _

local instance mixedBridgeLocalBlockL2Borel
    (U : TriadicCube 2) : BorelSpace (BlockL2 (openCubeSet U)) := ⟨rfl⟩

local instance mixedBridgeLocalBlockL2OpensMeasurable
    (U : TriadicCube 2) : OpensMeasurableSpace (BlockL2 (openCubeSet U)) :=
  ⟨le_of_eq rfl⟩

local instance mixedBridgeLocalHilbertOpensMeasurable
    (U : TriadicCube 2) : OpensMeasurableSpace (HilbertBlockL2 (openCubeSet U)) :=
  ⟨le_of_eq rfl⟩

local instance mixedBridgeLocalCubeCompact (U : TriadicCube 2) :
    CompactSpace (closure (cubeSet U)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet U).isCompact_closure

noncomputable def mixedBridgeVLocal (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  oldSignedPrimalErrorSize U U M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k

noncomputable def mixedBridgeGLocal (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  oldSignedReciprocalErrorSize U U M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k

/-- The actual local first-corrector weak square on one descendant of the
depth-five source cell. The canonical fields and their coefficient are rooted
at `U`, with the original insertion label and OLD frame `m`. -/
noncomputable def mixedBridgeLocalCorrectorSq' (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ)
    (V : SquareCells U j) : ℝ := by
  let hV : openCubeSet V.val ⊆ openCubeSet U :=
    openCubeSet_subset_of_mem_descendantsAtDepth V.property
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  exact ∑ a : BlockCoord 2,
    vectorWeakHaarNorm V.val (fun x =>
      (oldSignedCellFirstCorrector U V.val hV M.nu σ M.nu_pos hσ k
        (oldSignedFrameCanonicalField U M.nu σ M.nu_pos hσ k (blockBasis a))
        (Lp.memLp (oldSignedFrameCanonicalField U M.nu σ M.nu_pos hσ k (blockBasis a)))).toH1Function.grad x) ^ 2

/-- Finite descendant average of the actual local first-corrector square. -/
noncomputable def mixedBridgeVLocalDepthSq' (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  Cold.squareCellMean U j (mixedBridgeLocalCorrectorSq' M m U t ω j)

/-- The weighted depth series of the local first-corrector weak energies. -/
noncomputable def mixedBridgeVl2Local (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' j : ℕ,
    (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * mixedBridgeVLocalDepthSq' M m U t ω j

/-- The actual local first-corrector source size on `U`. -/
noncomputable def mixedBridgeVlLocal (M : ABKModel 2) (m : ℤ)
    (U : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Real.sqrt (mixedBridgeVl2Local M m U t ω)

private theorem mixed_bridge_local_response_coefficient_measurable
    (U : TriadicCube 2) (m : ℤ) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      mainAffineOpenResponseRestriction U
        (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)) := by
  let K := closure (cubeSet U)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isBounded_cubeSet U).isCompact_closure
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet U).isCompact_closure
  have hFresh : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction K (ω.1 (m + 1))) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hOlder : Measurable (fun ω : Cutoff.CutoffSample 2 => olderField K m ω) :=
    measurable_olderField K ell m hK
  have hf : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Gaussian.modelInsertedScalar K m t ω) := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    exact hOlder.add (hFresh.const_smul (Real.sqrt t))
  exact (mainAffineOpenResponseRestriction U).continuous.measurable.comp hf

private theorem mixed_bridge_local_canonical_field_measurable
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (P : BlockVec 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      oldSignedFrameCanonicalField U M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (mainAffineOpenResponseRestriction U
          (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)) P) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient (openCubeSet U) :=
    fun ω => mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let F : HilbertBlockL2 (openCubeSet U) := blockVecToHilbertBlockL2Const P
  have hResidual : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      scalarProjectionResidual U M.nu σ M.nu_pos hσ (coeff ω) F) :=
    measurable_scalarProjectionResidual_of_measurable_coefficient
      U M.nu σ M.nu_pos hσ coeff
      (mixed_bridge_local_response_coefficient_measurable U m t) F
  have hField : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      hilbertBlockL2ToBlockL2
        (scalarProjectionResidual U M.nu σ M.nu_pos hσ (coeff ω) F)) :=
    (hilbertBlockL2ToBlockL2 (U := openCubeSet U)).continuous.measurable.comp hResidual
  have hConst (ω : Cutoff.CutoffSample 2) :
      (scalarFrameRealization U M.nu σ M.nu_pos hσ (coeff ω)).constantField P = F := rfl
  have hEq : (fun ω : Cutoff.CutoffSample 2 =>
      oldSignedFrameCanonicalField U M.nu σ M.nu_pos hσ (coeff ω) P) =
      fun ω => hilbertBlockL2ToBlockL2
        (scalarProjectionResidual U M.nu σ M.nu_pos hσ (coeff ω) F) := by
    funext ω
    change oldSignedCanonicalAffineField U
      (responseFramePlanarCoefficientField M.nu σ (coeff ω))
      (responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet U) M.nu σ M.nu_pos hσ (coeff ω)) P = _
    rw [← old_signed_affine_residual_field U M.nu σ M.nu_pos hσ (coeff ω) P]
    rw [hConst ω]
    rfl
  rw [hEq]
  exact hField

private theorem mixed_bridge_local_potentialCoordinate_ae
    (U : TriadicCube 2) (i : Fin 2)
    (X : HilbertBlockL2 (openCubeSet U)) :
    hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2PotentialCLM X) =ᵐ[normalizedCubeMeasure U]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 i := by
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae U i
    (hilbertBlockL2PotentialCLM X)
  have hraw : hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 := by
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X),
      coeFn_hilbertBlockL2PotentialCLM X, coeFn_hilbertBlockL2ToBlockL2 X]
      with x hvec hpot hblock
    rw [hvec, hpot, hblock]
  have hdom : normalizedCubeMeasure U ≤
      ENNReal.ofReal ((cubeVolume U)⁻¹) • volumeMeasureOn (openCubeSet U) := by
    rw [normalizedCubeMeasure_eq_smul_open U]
  have habs : normalizedCubeMeasure U ≪ volumeMeasureOn (openCubeSet U) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hraw' : hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X) =ᵐ[
      normalizedCubeMeasure U] fun x => (hilbertBlockL2ToBlockL2 X x).1 :=
    habs.ae_eq hraw
  exact hcoord.trans (hraw'.mono fun x hx => congrArg (fun v : Vec 2 => v i) hx)

private theorem mixed_bridge_local_fluxCoordinate_ae
    (U : TriadicCube 2) (i : Fin 2)
    (X : HilbertBlockL2 (openCubeSet U)) :
    hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2FluxCLM X) =ᵐ[normalizedCubeMeasure U]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 i := by
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae U i
    (hilbertBlockL2FluxCLM X)
  have hraw : hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X) =ᵐ[
      volumeMeasureOn (openCubeSet U)]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := by
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X),
      coeFn_hilbertBlockL2FluxCLM X, coeFn_hilbertBlockL2ToBlockL2 X]
      with x hvec hflux hblock
    rw [hvec, hflux, hblock]
  have hdom : normalizedCubeMeasure U ≤
      ENNReal.ofReal ((cubeVolume U)⁻¹) • volumeMeasureOn (openCubeSet U) := by
    rw [normalizedCubeMeasure_eq_smul_open U]
  have habs : normalizedCubeMeasure U ≪ volumeMeasureOn (openCubeSet U) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hraw' : hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X) =ᵐ[
      normalizedCubeMeasure U] fun x => (hilbertBlockL2ToBlockL2 X x).2 :=
    habs.ae_eq hraw
  exact hcoord.trans (hraw'.mono fun x hx => congrArg (fun v : Vec 2 => v i) hx)

private theorem mixed_bridge_local_dualEnergy_congr_ae
    (U : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[normalizedCubeMeasure U] g) :
    dualEnergy U (Real.sqrt 3) f = dualEnergy U (Real.sqrt 3) g := by
  have hraw : volumeMeasureOn (openCubeSet U) =
      ENNReal.ofReal (cubeVolume U) • normalizedCubeMeasure U := by
    rw [normalizedCubeMeasure_eq_smul_open U, smul_smul]
    have hcoeff : ENNReal.ofReal (cubeVolume U) *
        ENNReal.ofReal ((cubeVolume U)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul (cubeVolume_pos U).le]
      rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos U)), ENNReal.ofReal_one]
    rw [hcoeff, one_smul]
  have hdom : volume.restrict (cubeSet U) ≤
      ENNReal.ofReal (cubeVolume U) • normalizedCubeMeasure U := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet U]
    exact le_of_eq hraw
  have habs : volume.restrict (cubeSet U) ≪ normalizedCubeMeasure U :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hfg' : f =ᵐ[volume.restrict (cubeSet U)] g := habs.ae_eq hfg
  have hinc (j : ℕ) := diagCubeIncrement_congr_ae U j hfg'
  unfold dualEnergy primalEnergy
  simp_rw [hinc]

private theorem mixed_bridge_local_primalEnergy_measurable
    {Ω : Type*} [MeasurableSpace Ω] (U : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    (q : ℝ) (hq : 0 ≤ q)
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure U)) (hu : Measurable u) :
    Measurable (fun ω => primalEnergy U q (fun x => u ω x)) := by
  classical
  let a : ℕ → Ω → ℝ := fun n ω =>
    q ^ (n + 1) * ‖cubeIncrementL2CLM U (n + 1) (u ω)‖ ^ 2
  let S : Ω → ENNReal := fun ω => ∑' n, ENNReal.ofReal (a n ω)
  have ha (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    have hn : Measurable (fun ω =>
        ‖cubeIncrementL2CLM U (n + 1) (u ω)‖ ^ 2) :=
      (((cubeIncrementL2CLM U (n + 1)).continuous.measurable.comp hu).norm.pow_const 2)
    simpa only [mul_comm] using hn.const_mul (q ^ (n + 1))
  have ha_nonneg (n : ℕ) (ω : Ω) : 0 ≤ a n ω := by
    dsimp [a]
    exact mul_nonneg (pow_nonneg hq _) (sq_nonneg _)
  have hS : Measurable S := by
    dsimp [S]
    exact Measurable.ennreal_tsum fun n => (ha n).ennreal_ofReal
  have htsum (ω : Ω) : (∑' n, a n ω) = (S ω).toReal := by
    by_cases htop : S ω = ∞
    · have hnot : ¬ Summable (fun n => a n ω) := by
        intro hs
        have hfinite := hs.tsum_ofReal_ne_top
        have hSfinite : S ω ≠ ∞ := by
          intro hInf
          exact hfinite (by simpa [S] using hInf)
        exact hSfinite htop
      rw [tsum_eq_zero_of_not_summable hnot, htop]
      rfl
    · let b : ℕ → NNReal := fun n => Real.toNNReal (a n ω)
      have hb (n : ℕ) : (b n : ENNReal) = ENNReal.ofReal (a n ω) := by
        simp [b, ENNReal.ofReal, Real.toNNReal_of_nonneg (ha_nonneg n ω)]
      have hsumB : Summable b := by
        apply (ENNReal.tsum_coe_ne_top_iff_summable).mp
        rw [show (∑' n, (b n : ENNReal)) = S ω from by
          apply tsum_congr
          intro n
          exact hb n]
        exact htop
      have hsumReal : Summable (fun n => (b n : ℝ)) := NNReal.summable_coe.2 hsumB
      have hEq : (fun n => (b n : ℝ)) = fun n => a n ω := by
        funext n
        dsimp [b]
        exact Real.coe_toNNReal _ (ha_nonneg n ω)
      have hsumA : Summable (fun n => a n ω) := hEq ▸ hsumReal
      have hrepr : ENNReal.ofReal (∑' n, a n ω) = S ω := by
        dsimp [S]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nonneg n ω) hsumA
      have hsum_nonneg : 0 ≤ (∑' n, a n ω) := tsum_nonneg fun n => ha_nonneg n ω
      calc
        (∑' n, a n ω) = (ENNReal.ofReal (∑' n, a n ω)).toReal :=
          (ENNReal.toReal_ofReal hsum_nonneg).symm
        _ = (S ω).toReal := by rw [hrepr]
  have hbaseEq : (fun ω => energy U (cubeIncrement U 0 (fun x => u ω x))) =
      fun ω => ‖cubeIncrementL2CLM U 0 (u ω)‖ ^ 2 := by
    funext ω
    exact energy_cubeIncrement_eq_clm_norm_sq U 0 (u ω)
  have hbase : Measurable
      (fun ω => energy U (cubeIncrement U 0 (fun x => u ω x))) := by
    rw [hbaseEq]
    exact (((cubeIncrementL2CLM U 0).continuous.measurable.comp hu).norm.pow_const 2)
  have hEq (ω : Ω) : primalEnergy U q (fun x => u ω x) =
      energy U (cubeIncrement U 0 (fun x => u ω x)) + (S ω).toReal := by
    rw [primalEnergy]
    have hterm (n : ℕ) : q ^ (n + 1) * energy U
        (cubeIncrement U (n + 1) (fun x => u ω x)) = a n ω := by
      rw [energy_cubeIncrement_eq_clm_norm_sq]
    rw [tsum_congr hterm, htsum ω]
  have hresult : Measurable
      (fun ω => energy U (cubeIncrement U 0 (fun x => u ω x)) + (S ω).toReal) :=
    hbase.add hS.ennreal_toReal
  rw [show (fun ω => primalEnergy U q (fun x => u ω x)) =
      fun ω => energy U (cubeIncrement U 0 (fun x => u ω x)) + (S ω).toReal from by
        funext ω
        exact hEq ω]
  exact hresult

private theorem mixed_bridge_local_dualEnergy_measurable
    {Ω : Type*} [MeasurableSpace Ω] (U : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure U)) (hu : Measurable u) :
    Measurable (fun ω => dualEnergy U (Real.sqrt 3) (fun x => u ω x)) := by
  unfold dualEnergy
  exact mixed_bridge_local_primalEnergy_measurable U
    ((Real.sqrt 3)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg _)) u hu

private theorem mixed_bridge_local_v2_measurable
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      mixedBridgeVLocal M m U t ω ^ 2) := by
  classical
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient (openCubeSet U) :=
    fun ω => mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let can (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : BlockL2 (openCubeSet U) :=
    oldSignedFrameCanonicalField U M.nu σ M.nu_pos hσ (coeff ω) (blockBasis a)
  let X (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) :
      HilbertBlockL2 (openCubeSet U) := blockL2ToHilbertBlockL2 (can a ω)
  let u (a : BlockCoord 2) (i : Fin 2) (ω : Cutoff.CutoffSample 2) :
      Lp ℝ 2 (normalizedCubeMeasure U) :=
    hilbertVectorL2_normalizedCoordCLM U i
      (hilbertBlockL2PotentialCLM (X a ω)) -
        Lp.const 2 (normalizedCubeMeasure U) ((blockBasis a).1 i)
  letI : MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U)) := borel _
  letI : BorelSpace (Lp ℝ 2 (normalizedCubeMeasure U)) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U)) := ⟨le_of_eq rfl⟩
  letI : IsSeparable (volumeMeasureOn (openCubeSet U)) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet U)) := inferInstance
  have hcoeff : Measurable coeff :=
    mixed_bridge_local_response_coefficient_measurable U m t
  have hcan (a : BlockCoord 2) : Measurable (can a) := by
    simpa [can, coeff, σ, hσ] using
      mixed_bridge_local_canonical_field_measurable M m U t (blockBasis a)
  have hX (a : BlockCoord 2) : Measurable (X a) :=
    (blockL2ToHilbertBlockL2 (U := openCubeSet U)).continuous.measurable.comp (hcan a)
  have hCoord (a : BlockCoord 2) (i : Fin 2) : Measurable (fun ω =>
      hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2PotentialCLM (X a ω))) :=
    (hilbertVectorL2_normalizedCoordCLM U i).continuous.measurable.comp
      ((hilbertBlockL2PotentialCLM (U := openCubeSet U)).continuous.measurable.comp (hX a))
  have hu (a : BlockCoord 2) (i : Fin 2) : Measurable (u a i) := by
    dsimp [u]
    exact (hCoord a i).sub measurable_const
  have hdual (a : BlockCoord 2) (i : Fin 2) :
      Measurable (fun ω => dualEnergy U (Real.sqrt 3) (fun x => u a i ω x)) :=
    mixed_bridge_local_dualEnergy_measurable U (u a i) (hu a i)
  have hcoordinateIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarNorm U (fun x => (can a ω x).1 - (blockBasis a).1) ^ 2 =
        ∑ i : Fin 2, dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    rw [vectorWeakHaarNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    have hXeq : hilbertBlockL2ToBlockL2 (X a ω) = can a ω :=
      hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2 (can a ω)
    have hpot := mixed_bridge_local_potentialCoordinate_ae U i (X a ω)
    have hpot' : hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2PotentialCLM (X a ω)) =ᵐ[normalizedCubeMeasure U]
          fun x => (can a ω x).1 i := by
      rw [hXeq] at hpot
      exact hpot
    have hsub := mixed_bridge_local_dualEnergy_congr_ae U
      (show u a i ω =ᵐ[normalizedCubeMeasure U]
        fun x => ((can a ω x).1 - (blockBasis a).1) i from by
          filter_upwards [Lp.coeFn_sub
              (hilbertVectorL2_normalizedCoordCLM U i
                (hilbertBlockL2PotentialCLM (X a ω)))
              (Lp.const 2 (normalizedCubeMeasure U) ((blockBasis a).1 i)),
            Lp.coeFn_const (p := (2 : ℝ≥0∞))
              (μ := normalizedCubeMeasure U) (c := ((blockBasis a).1 i)), hpot']
            with x hsub hconst hfield
          calc
            u a i ω x =
                (hilbertVectorL2_normalizedCoordCLM U i
                    (hilbertBlockL2PotentialCLM (X a ω)) -
                  Lp.const 2 (normalizedCubeMeasure U) ((blockBasis a).1 i) :
                    Lp ℝ 2 (normalizedCubeMeasure U)) x := by rfl
            _ = hilbertVectorL2_normalizedCoordCLM U i
                  (hilbertBlockL2PotentialCLM (X a ω)) x -
                (Lp.const 2 (normalizedCubeMeasure U) ((blockBasis a).1 i) :
                  Lp ℝ 2 (normalizedCubeMeasure U)) x := hsub
            _ = (can a ω x).1 i - (blockBasis a).1 i := by
              rw [hfield, hconst]
              simp
            _ = ((can a ω x).1 - (blockBasis a).1) i := rfl)
    change weakHaarNorm U (fun x => ((can a ω x).1 - (blockBasis a).1) i) ^ 2 = _
    rw [weakHaarNorm, Real.sq_sqrt (dualEnergy_nonneg U (Real.sqrt 3)
      (Real.sqrt_nonneg _) (fun x => ((can a ω x).1 - (blockBasis a).1) i))]
    exact hsub.symm
  have henergyIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarEnergy U (fun x => (can a ω x).1 - (blockBasis a).1) =
        ∑ i : Fin 2, dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    have hh := hcoordinateIdentity ω a
    rw [vectorWeakHaarNorm_sq] at hh
    simp only [weakHaarNorm,
      Real.sq_sqrt (dualEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) _)] at hh
    simpa [vectorWeakHaarEnergy] using hh
  have hsum : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy U (Real.sqrt 3) (fun x => u a i ω x)) := by
    apply Finset.measurable_sum
    intro a ha
    apply Finset.measurable_sum
    intro i hi
    exact hdual a i
  have hEq : (fun ω : Cutoff.CutoffSample 2 => mixedBridgeVLocal M m U t ω ^ 2) =
      fun ω => ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    funext ω
    rw [mixedBridgeVLocal, old_signed_primal_error_size_sq]
    apply Finset.sum_congr rfl
    intro a ha
    exact henergyIdentity ω a
  rw [hEq]
  exact hsum

private theorem mixed_bridge_local_measurable
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      mixedBridgeGLocal M m U t ω ^ 2) := by
  classical
  let ν : ℝ := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient (openCubeSet U) :=
    fun ω => mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let can (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : BlockL2 (openCubeSet U) :=
    oldSignedFrameCanonicalField U ν σ hν hσ (coeff ω) (blockBasis a)
  let X (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) :
      HilbertBlockL2 (openCubeSet U) := blockL2ToHilbertBlockL2 (can a ω)
  let T (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) :
      HilbertBlockL2 (openCubeSet U) :=
    X a ω + responseShearL2Operator σ hσ (coeff ω) (X a ω)
  let u (a : BlockCoord 2) (i : Fin 2) (ω : Cutoff.CutoffSample 2) :
      Lp ℝ 2 (normalizedCubeMeasure U) :=
    (σ / ν) • hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2FluxCLM (T a ω)) -
      Lp.const 2 (normalizedCubeMeasure U) (((blockBasis a).2) i)
  letI : MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U)) := borel _
  letI : BorelSpace (Lp ℝ 2 (normalizedCubeMeasure U)) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U)) := ⟨le_of_eq rfl⟩
  letI : IsSeparable (volumeMeasureOn (openCubeSet U)) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet U)) := inferInstance
  letI : OpensMeasurableSpace
      ((HilbertBlockL2 (openCubeSet U) →L[ℝ] HilbertBlockL2 (openCubeSet U)) ×
        HilbertBlockL2 (openCubeSet U)) := inferInstance
  have hcoeff : Measurable coeff :=
    mixed_bridge_local_response_coefficient_measurable U m t
  have hcan (a : BlockCoord 2) : Measurable (can a) := by
    simpa [can, coeff, ν, σ, hν, hσ] using
      mixed_bridge_local_canonical_field_measurable M m U t (blockBasis a)
  have hX (a : BlockCoord 2) : Measurable (X a) :=
    (blockL2ToHilbertBlockL2 (U := openCubeSet U)).continuous.measurable.comp (hcan a)
  have hOp : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      responseShearL2Operator σ hσ (coeff ω)) :=
    (responseShearL2Family (measurableSet_openCubeSet U) σ hσ).continuous.measurable.comp
      hcoeff
  have hShear (a : BlockCoord 2) : Measurable (fun ω =>
      responseShearL2Operator σ hσ (coeff ω) (X a ω)) := by
    have hev : Continuous fun p :
        (HilbertBlockL2 (openCubeSet U) →L[ℝ] HilbertBlockL2 (openCubeSet U)) ×
          HilbertBlockL2 (openCubeSet U) => p.1 p.2 := by fun_prop
    exact hev.measurable.comp (hOp.prodMk (hX a))
  have hT (a : BlockCoord 2) : Measurable (T a) := (hX a).add (hShear a)
  have hFlux (a : BlockCoord 2) : Measurable (fun ω =>
      hilbertBlockL2FluxCLM (T a ω)) :=
    (hilbertBlockL2FluxCLM (U := openCubeSet U)).continuous.measurable.comp (hT a)
  have hCoord (a : BlockCoord 2) (i : Fin 2) : Measurable (fun ω =>
      hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2FluxCLM (T a ω))) :=
    (hilbertVectorL2_normalizedCoordCLM U i).continuous.measurable.comp (hFlux a)
  have hu (a : BlockCoord 2) (i : Fin 2) : Measurable (u a i) := by
    dsimp [u]
    exact ((hCoord a i).const_smul (σ / ν)).sub measurable_const
  have hdual (a : BlockCoord 2) (i : Fin 2) :
      Measurable (fun ω => dualEnergy U (Real.sqrt 3) (fun x => u a i ω x)) :=
    mixed_bridge_local_dualEnergy_measurable U (u a i) (hu a i)
  have hcoordinateAE (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2)
      (i : Fin 2) :
      u a i ω =ᵐ[normalizedCubeMeasure U]
        fun x => ((blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (can a ω x)).2 - (blockBasis a).2) i := by
    let F := can a ω
    let Xω := X a ω
    let Tω := T a ω
    let W := hilbertBlockL2FluxCLM Tω
    have hFluxCoord := mixed_bridge_local_fluxCoordinate_ae U i Tω
    have hPointwiseShear :
        (fun x => (hilbertBlockL2ToBlockL2 Tω x).2) =ᵐ[
          volumeMeasureOn (openCubeSet U)]
          fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (hilbertBlockL2ToBlockL2 Xω x)).2 := by
      have hs := responseShearAffineL2_toBlockL2_ae σ hσ (coeff ω) Xω
      filter_upwards [hs] with x hx
      exact congrArg Prod.snd hx
    have hdom : normalizedCubeMeasure U ≤
        ENNReal.ofReal ((cubeVolume U)⁻¹) • volumeMeasureOn (openCubeSet U) := by
      rw [normalizedCubeMeasure_eq_smul_open U]
    have habs : normalizedCubeMeasure U ≪ volumeMeasureOn (openCubeSet U) :=
      Measure.absolutelyContinuous_of_le_smul hdom
    have hPointwiseShear' :
        (fun x => (hilbertBlockL2ToBlockL2 Tω x).2) =ᵐ[
          normalizedCubeMeasure U]
          fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (hilbertBlockL2ToBlockL2 Xω x)).2 := habs.ae_eq hPointwiseShear
    have hflux := hFluxCoord.trans (hPointwiseShear'.mono
      (fun x hx => congrArg (fun v : Vec 2 => v i) hx))
    have hXrep : hilbertBlockL2ToBlockL2 Xω =ᵐ[
        volumeMeasureOn (openCubeSet U)] F := by
      rw [hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2]
    have hXrep' : hilbertBlockL2ToBlockL2 Xω =ᵐ[normalizedCubeMeasure U] F :=
      habs.ae_eq hXrep
    have hlower (x : Vec 2) :
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (F x)).2 = lemmaVConjugateGradient ν σ
            (responseCoefficientExtension (coeff ω) x) (F x) := by
      have h := lemmaV_planar_lower_image ν σ
        (responseCoefficientExtension (coeff ω) x) hν hσ (F x)
      simpa [responseFramePlanarCoefficientField, blockCoeffField] using h
    have hShearIdentity (x : Vec 2) :
        lemmaVConjugateGradient ν σ (responseCoefficientExtension (coeff ω) x) (F x) =
          (σ / ν) • (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (F x)).2 := by
      ext j
      simp [lemmaVConjugateGradient, responseShear, responseShearCorrection,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    have hShearRep :
        (fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (hilbertBlockL2ToBlockL2 Xω x)).2 i) =ᵐ[normalizedCubeMeasure U]
          fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (F x)).2 i := hXrep'.mono (fun x hx => congrArg
              (fun z : BlockVec 2 =>
                (responseShear σ (responseCoefficientExtension (coeff ω) x) z).2 i) hx)
    have hcombine := hflux.trans hShearRep
    have hcombine' :
        (fun x => (σ / ν) * hilbertVectorL2_normalizedCoordCLM U i W x) =ᵐ[
          normalizedCubeMeasure U]
          fun x => (σ / ν) *
            (responseShear σ (responseCoefficientExtension (coeff ω) x) (F x)).2 i :=
      hcombine.mono (fun x hx => congrArg (fun z : ℝ => (σ / ν) * z) hx)
    have hfinal :
        (σ / ν) • hilbertVectorL2_normalizedCoordCLM U i W -
            Lp.const 2 (normalizedCubeMeasure U) (((blockBasis a).2) i) =ᵐ[
              normalizedCubeMeasure U]
          fun x => ((blockMatVecMul
            (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
            (F x)).2 - (blockBasis a).2) i := by
      filter_upwards [Lp.coeFn_sub
          ((σ / ν) • hilbertVectorL2_normalizedCoordCLM U i W)
          (Lp.const 2 (normalizedCubeMeasure U) (((blockBasis a).2) i)),
        Lp.coeFn_smul (σ / ν) (hilbertVectorL2_normalizedCoordCLM U i W),
        Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure U)
          (c := (((blockBasis a).2) i)), hcombine'] with x hsub hsmul hconst hcomb
      calc
        ((σ / ν) • hilbertVectorL2_normalizedCoordCLM U i W -
            Lp.const 2 (normalizedCubeMeasure U) (((blockBasis a).2) i) :
            Lp ℝ 2 (normalizedCubeMeasure U)) x =
            ((σ / ν) • hilbertVectorL2_normalizedCoordCLM U i W :
              Lp ℝ 2 (normalizedCubeMeasure U)) x -
              (Lp.const 2 (normalizedCubeMeasure U) (((blockBasis a).2) i) :
                Lp ℝ 2 (normalizedCubeMeasure U)) x := hsub
        _ = (σ / ν) * hilbertVectorL2_normalizedCoordCLM U i W x -
            ((blockBasis a).2) i := by
          rw [hsmul, hconst]
          simp [smul_eq_mul]
        _ = (σ / ν) * (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (F x)).2 i - ((blockBasis a).2) i := by rw [hcomb]
        _ = ((blockMatVecMul
            (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
            (F x)).2 - (blockBasis a).2) i := by
          rw [hlower x, hShearIdentity x]
          simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simpa only [u, T, X, can, coeff, ν, σ, hν, hσ, W, Tω, Xω, F] using hfinal
  have hcoordinateIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarNorm U (fun x =>
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (can a ω x)).2 - (blockBasis a).2) ^ 2 =
        ∑ i : Fin 2, dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    rw [vectorWeakHaarNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    have hAE := hcoordinateAE ω a i
    have hde := mixed_bridge_local_dualEnergy_congr_ae U hAE.symm
    change weakHaarNorm U (fun x =>
      ((blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
        (can a ω x)).2 - (blockBasis a).2) i) ^ 2 = _
    rw [weakHaarNorm, Real.sq_sqrt (dualEnergy_nonneg U (Real.sqrt 3)
      (Real.sqrt_nonneg _) _)]
    exact hde
  have henergyIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarEnergy U (fun x =>
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (can a ω x)).2 - (blockBasis a).2) =
        ∑ i : Fin 2, dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    have hh := hcoordinateIdentity ω a
    rw [vectorWeakHaarNorm_sq] at hh
    simp only [weakHaarNorm,
      Real.sq_sqrt (dualEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) _)] at hh
    simpa [vectorWeakHaarEnergy] using hh
  have hsum : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy U (Real.sqrt 3) (fun x => u a i ω x)) := by
    apply Finset.measurable_sum
    intro a ha
    apply Finset.measurable_sum
    intro i hi
    exact hdual a i
  have hEq : (fun ω : Cutoff.CutoffSample 2 => mixedBridgeGLocal M m U t ω ^ 2) =
      fun ω => ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    funext ω
    rw [mixedBridgeGLocal, old_signed_reciprocal_error_size_sq]
    apply Finset.sum_congr rfl
    intro a ha
    simpa [oldSignedDualReflection, can, coeff, ν, σ, hν, hσ] using
      henergyIdentity ω a
  rw [hEq]
  exact hsum

private theorem mixed_bridge_bank_response_max_eq_finsetSup
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty)
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    bankFiniteRootResponseMax s M m J weights ω =
      ENNReal.ofReal (Book.Ch02.finsetSupReal s
        (fun R => rootInverseResponse M R m J weights ω)) := by
  classical
  have huniv : (Finset.univ : Finset ↥s) = s.attach := by
    ext R
    simp
  calc
    bankFiniteRootResponseMax s M m J weights ω =
        (Finset.univ : Finset ↥s).sup
          (fun R => ENNReal.ofReal (rootInverseResponse M R.1 m J weights ω)) := by
      simp only [bankFiniteRootResponseMax, historyFiniteMax]
    _ = s.attach.sup
        (fun R => ENNReal.ofReal (rootInverseResponse M R.1 m J weights ω)) := by
      rw [huniv]
    _ = s.sup (fun R => ENNReal.ofReal (rootInverseResponse M R m J weights ω)) :=
      Finset.sup_attach s (fun R => ENNReal.ofReal (rootInverseResponse M R m J weights ω))
    _ = ENNReal.ofReal (Book.Ch02.finsetSupReal s
        (fun R => rootInverseResponse M R m J weights ω)) :=
      (ennreal_finset_sup_ofReal s hs _).symm

attribute [local irreducible] Homogenization.descendantsAtDepth

private theorem mixed_bridge_local_depth_inverse_max_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) 5)
    (j : ℕ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      lemmaVInverseDepthMax U
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainAffineOpenResponseRestriction U
            (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω))) j ≤
        mixedOldDepthCoefficient M m t j ω := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M m
  let coeff (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet U) :=
    mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let a (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
    responseFramePlanarCoefficientField M.nu σ (coeff ω)
  let c (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
    (Model.partialInsertedCoefficient M m t ω).toFun
  let root : TriadicCube 2 := originCube 2 (m + 40)
  let weights : ℤ → ℝ := bankPartialInsertionWeights m 1 t
  let D : Finset (TriadicCube 2) := bankObserverDepthRootUnion root 5 j
  have hparent : originCube 2 m ∈ bankObserverRoots root 0 := by
    rw [bankObserverRoots]
    exact originCube_mem_descendantsAtOffset 2 m 40
  have hUObserver : U ∈ bankObserverRoots root 5 := by
    have hdepth := mem_descendantsAtDepth_add hparent hU
    simpa [bankObserverRoots, root] using hdepth
  have hJ : m ≤ m + 40 := by omega
  have hweights : ∀ k ∈ Finset.Ioc m (m + 40),
      0 ≤ weights k ∧ weights k ≤ 1 := by
    intro k hk
    exact bank_partial_insertion_weights_bounds m 1 t ht.2 k
  have hpastM : ∀ n < m, nativeInductionState M h n := by
    intro n hn
    exact hpast n (hn.trans hm)
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hγ m hpastM).2
  have hrootScale : root.scale = m + 40 := rfl
  have hbank : InverseBankDepthBlockConclusion M .localInverse D m (m + 40)
      weights j := by
    simpa only [D, root, weights] using
      (inverse_bank_observer_union_depths M h hM hγ .localInverse root m (m + 40)
        hrootScale hJ weights hweights 5 le_rfl hpastM hmean j).2
  filter_upwards [hbank.block_finite, hbank.block_le] with ω hfinite hblock
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet U)) (isBounded_cubeSet U).isCompact_closure
  have hEllCopen : IsEllipticFieldOn M.nu
      ((2 * 2 * (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (openCubeSet U) (c ω) := by
    exact Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω
      ⟨ht.1, ht.2⟩ (measurableSet_openCubeSet U)
      (fun x hx => hK (subset_closure (openCubeSet_subset_cubeSet U hx)))
  have hmatrix (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) (a ω) =
        frameMatrix σ (coarseBlockMatrix (cubeSet V) (c ω)) := by
    simpa [a, c, coeff, σ, oldSignedPartialFrameFieldAt] using
      old_signed_partial_cell_frame_at M U m t ω V j hV
  have hlocalFrame : lemmaVInverseDepthMax U (a ω) j =
      σ * lemmaVInverseDepthMax U (c ω) j := by
    exact pureFlux_inverseDepthMax_frame_eq U (c ω) (a ω) hEllCopen
      (responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet U) M.nu σ M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 (coeff ω))
      (Annealed.sigmaBar_characterization M m).1 j hmatrix
  have hcoeff : attenuatedCoefficient M m (m + 40) weights ω = c ω := by
    dsimp [c, weights]
    calc
      _ = (Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun :=
        bank_one_pass_partial_coefficient M m 1 (by norm_num) t ω
      _ = _ := by rw [show m + (1 : ℤ) - 1 = m by omega]
  have hsourceMax : bankFiniteRootResponseMax (descendantsAtDepth U j)
      M m (m + 40) weights ω =
        ENNReal.ofReal (σ * lemmaVInverseDepthMax U (c ω) j) :=
    bank_depth_max_physical U M m (m + 40) weights ω (c ω) hcoeff hEllCopen j
  have hsub (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U j) : V ∈ D := by
    unfold D bankObserverDepthRootUnion
    refine Finset.mem_biUnion.mpr ⟨5, Finset.mem_range.mpr (by omega), ?_⟩
    exact bank_observer_depth_roots_mem root 5 j hUObserver hV
  have hlocalNonempty : (descendantsAtDepth U j).Nonempty :=
    descendantsAtDepth_nonempty U j
  have hDnonempty : D.Nonempty := by
    obtain ⟨V, hV⟩ := hlocalNonempty
    exact ⟨V, hsub V hV⟩
  let f : TriadicCube 2 → ℝ := fun V =>
    rootInverseResponse M V m (m + 40) weights ω
  have hlocalSupEq : bankFiniteRootResponseMax (descendantsAtDepth U j)
      M m (m + 40) weights ω = ENNReal.ofReal
        (Book.Ch02.finsetSupReal (descendantsAtDepth U j) f) := by
    simpa only [f] using mixed_bridge_bank_response_max_eq_finsetSup
      (descendantsAtDepth U j) hlocalNonempty M m (m + 40) weights ω
  have hunionSupEq : bankFiniteRootResponseMax D M m (m + 40) weights ω =
      ENNReal.ofReal (Book.Ch02.finsetSupReal D f) := by
    simpa only [f] using mixed_bridge_bank_response_max_eq_finsetSup
      D hDnonempty M m (m + 40) weights ω
  have hsup : Book.Ch02.finsetSupReal (descendantsAtDepth U j) f ≤
      Book.Ch02.finsetSupReal D f := by
    apply Book.Ch02.finsetSupReal_le (descendantsAtDepth U j) hlocalNonempty
    intro V hV
    exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal D f (hsub V hV)
  have hmax :
      bankFiniteRootResponseMax (descendantsAtDepth U j) M m (m + 40) weights ω ≤
        bankFiniteRootResponseMax D M m (m + 40) weights ω := by
    rw [hlocalSupEq, hunionSupEq]
    exact ENNReal.ofReal_le_ofReal hsup
  have hcap0 : 0 ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j := by
    exact mul_nonneg (by norm_num [inverseBankCap]) (bankDepthFrame_pos M j).le
  have hremainder0 :
      0 ≤ inverseBankDepthBlockRemainder .localInverse D M m (m + 40) weights j ω :=
    hbank.remainder_nonneg ω
  have hphysical0 : 0 ≤ σ * lemmaVInverseDepthMax U (c ω) j :=
    mul_nonneg (Annealed.sigmaBar_characterization M m).1.le
      (lemmaVInverseDepthMax_nonneg U (c ω) j)
  have hsum0 :
      0 ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
        inverseBankDepthBlockRemainder .localInverse D M m (m + 40) weights j ω :=
    add_nonneg hcap0 hremainder0
  have hle := hmax.trans hblock
  have hsumFinite :
      ENNReal.ofReal ((inverseBankCap .localInverse : ℝ) * bankDepthFrame M j) +
        ENNReal.ofReal (inverseBankDepthBlockRemainder .localInverse D M m
          (m + 40) weights j ω) < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  have hreal := ENNReal.toReal_mono hsumFinite.ne hle
  rw [hsourceMax, ENNReal.toReal_ofReal hphysical0, ENNReal.toReal_add
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hcap0, ENNReal.toReal_ofReal hremainder0] at hreal
  have hbound : lemmaVInverseDepthMax U (a ω) j ≤
      (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
        mixedOldLocalDepthRemainder M m t j ω := by
    calc
      lemmaVInverseDepthMax U (a ω) j ≤
          (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
            inverseBankDepthBlockRemainder .localInverse D M m (m + 40) weights j ω := by
        rw [hlocalFrame]
        exact hreal
      _ = (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
          mixedOldLocalDepthRemainder M m t j ω := by rfl
  simpa [mixedOldDepthCoefficient] using hbound

private theorem mixed_bridge_local_trace_cell_eq_raw
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (ω : Cutoff.CutoffSample 2)
    (a : CoeffField 2)
    (hframe : ∀ (j : ℕ) (V : TriadicCube 2),
      V ∈ descendantsAtDepth U j →
      coarseBlockMatrix (cubeSet V) a = frameMatrix
        (Annealed.sigmaBar M m : ℝ)
        (coarseBlockMatrix (cubeSet V)
          (Model.partialInsertedCoefficient M m t ω).toFun))
    (j : ℕ) (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U j) :
    traceDefect (openCubeSet V) a 1 = rawCubeFourLoadTrace M m V t ω := by
  let σ : ℝ := Annealed.sigmaBar M m
  let c : CoeffField 2 := (Model.partialInsertedCoefficient M m t ω).toFun
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet U)) (isBounded_cubeSet U).isCompact_closure
  have hVsub : cubeSet V ⊆ cubeSet U := cubeSet_subset_of_mem_descendantsAtDepth hV
  have hEll : IsEllipticFieldOn M.nu
      ((2 * 2 * (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (cubeSet V) c := by
    exact Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω
      ⟨ht.1, ht.2⟩ (measurableSet_cubeSet V)
      (fun x hx => hK (subset_closure (hVsub hx)))
  have hscaled : coarseBlockMatrix (cubeSet V) (σ⁻¹ • c) =
      frameMatrix σ (coarseBlockMatrix (cubeSet V) c) :=
    Cold.cold_coarse_frame M.nu_pos hEll (Annealed.sigmaBar_characterization M m).1
  have hcoarse : coarseBlockMatrix (cubeSet V) a =
      coarseBlockMatrix (cubeSet V) (σ⁻¹ • c) := (hframe j V hV).trans hscaled.symm
  have hcoarseOpen : coarseBlockMatrix (openCubeSet V) a =
      coarseBlockMatrix (openCubeSet V) (σ⁻¹ • c) := by
    rw [← Cold.cold_coarse_cube_open V a,
      ← Cold.cold_coarse_cube_open V (σ⁻¹ • c)]
    exact hcoarse
  have htrace : traceDefect (openCubeSet V) a 1 =
      traceDefect (openCubeSet V) (σ⁻¹ • c) 1 := by
    unfold traceDefect
    rw [hcoarseOpen]
  have hphysical := Cold.cold_trace_frame M.nu_pos hEll
    (Annealed.sigmaBar_characterization M m).1
  simpa only [rawCubeFourLoadTrace, σ, c] using htrace.trans hphysical

private theorem mixed_bridge_local_squareCellMean_eq_descendantsAverage
    (Q : TriadicCube 2) (j : ℕ) (f : TriadicCube 2 → ℝ) :
    Cold.squareCellMean Q j (fun C => f C.1) = descendantsAverage Q j f := by
  unfold Cold.squareCellMean descendantsAverage
  congr 1
  exact Finset.sum_attach (descendantsAtDepth Q j) f

private theorem mixed_bridge_local_trace_average_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    ∀ j : ℕ,
      descendantsAverage U j (fun V => traceDefect (openCubeSet V)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainAffineOpenResponseRestriction U
            (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω))) 1) =
        rawWeakTraceSequence M m U t ω j := by
  intro j
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
    (mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω))
  have hframe (q : ℕ) (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U q) :
      coarseBlockMatrix (cubeSet V) a = frameMatrix (Annealed.sigmaBar M m : ℝ)
        (coarseBlockMatrix (cubeSet V)
          (Model.partialInsertedCoefficient M m t ω).toFun) := by
    simpa [a, oldSignedPartialFrameFieldAt] using
      old_signed_partial_cell_frame_at M U m t ω V q hV
  have hcell (V : TriadicCube 2) (hV : V ∈ descendantsAtDepth U j) :
      traceDefect (openCubeSet V) a 1 = rawCubeFourLoadTrace M m V t ω :=
    mixed_bridge_local_trace_cell_eq_raw M m t ht U ω a hframe j V hV
  calc
    descendantsAverage U j (fun V => traceDefect (openCubeSet V) a 1) =
        descendantsAverage U j (fun V => rawCubeFourLoadTrace M m V t ω) := by
      unfold descendantsAverage
      dsimp only
      apply congrArg (fun z : ℝ => ((descendantsAtDepth U j).card : ℝ)⁻¹ * z)
      apply Finset.sum_congr rfl
      intro V hV
      exact hcell V hV
    _ = rawWeakTraceSequence M m U t ω j := by
      unfold rawWeakTraceSequence
      exact (mixed_bridge_local_squareCellMean_eq_descendantsAverage U j
        (fun V => rawCubeFourLoadTrace M m V t ω)).symm

private theorem mixed_bridge_local_primal_gap_proxy
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalErrorSize Q Q nu sigma hnu hsigma k ^ 2 ≤
      rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j
          (fun V => traceDefect (openCubeSet V) a 1) - traceDefect (openCubeSet Q) a 1) := by
  classical
  dsimp only
  let a := responseFramePlanarCoefficientField nu sigma k
  let α := Scalar.inverseHistoryDiscount
  let F : BlockCoord 2 → Vec 2 → Vec 2 := fun c x =>
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x).1 -
      (blockBasis c).1
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hF (c : BlockCoord 2) (i : Fin 2) :
      MemLp (fun x => F c x i) 2 (normalizedCubeMeasure Q) := by
    have hm := (memVectorL2_fst_of_memBlockL2
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c)))).sub
      (memVectorL2_const (blockBasis c).1)
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hm i)
  have hseries := old_signed_finite_weak_projection_series Q F hF
  have hgap (j : ℕ) : 0 ≤ descendantsAverage Q j
      (fun V => traceDefect (openCubeSet V) a 1) - traceDefect (openCubeSet Q) a 1 := by
    have hparent := old_signed_parent_trace_le_child Q j nu sigma hnu hsigma k
    simpa only [a] using sub_nonneg.mpr hparent
  have hdepth (j : ℕ) :
      (∑ c : BlockCoord 2, ∑ i : Fin 2,
        energy Q (cubeProjection Q j (fun x => F c x i))) ≤
      lemmaVInverseDepthMax Q a j *
        (descendantsAverage Q j (fun V => traceDefect (openCubeSet V) a 1) -
          traceDefect (openCubeSet Q) a 1) := by
    have hproj := old_signed_primal_projection_trace_gap Q j nu sigma hnu hsigma k
    simpa [F, a, oldSignedPrimalProjectionEnergy] using hproj
  have hgapLe (j : ℕ) :
      descendantsAverage Q j (fun V => traceDefect (openCubeSet V) a 1) -
          traceDefect (openCubeSet Q) a 1 ≤
        descendantsAverage Q j (fun V => traceDefect (openCubeSet V) a 1) := by
    exact sub_le_self _ (Cold.coarse_square_traceDefect_nonneg Q hEll)
  have hTnonneg (j : ℕ) : 0 ≤ descendantsAverage Q j
      (fun V => traceDefect (openCubeSet V) a 1) := by
    apply descendantsAverage_nonneg
    intro V hV
    exact Cold.coarse_square_traceDefect_nonneg V
      (hEll.mono (measurableSet_openCubeSet V)
        (openCubeSet_subset_of_mem_descendantsAtDepth hV))
  have hproxy := old_signed_weak_trace_proxy_summable Q a hEll
  have hgapSeries : Summable (fun j : ℕ => α ^ (2 * j) *
      lemmaVInverseDepthMax Q a j *
        (descendantsAverage Q j (fun V => traceDefect (openCubeSet V) a 1) -
          traceDefect (openCubeSet Q) a 1)) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
        (lemmaVInverseDepthMax_nonneg Q a j)) (hgap j)
    · intro j
      exact mul_le_mul_of_nonneg_left (hgapLe j)
        (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
          (lemmaVInverseDepthMax_nonneg Q a j))
    · exact hproxy
  have hcompare := hseries.1.tsum_le_tsum (fun j => by
      simpa only [α, ← mul_assoc] using mul_le_mul_of_nonneg_left (hdepth j)
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))) hgapSeries
  have hVeq : oldSignedPrimalErrorSize Q Q nu sigma hnu hsigma k ^ 2 =
      (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) *
        (∑ c : BlockCoord 2, ∑ i : Fin 2,
          energy Q (cubeProjection Q j (fun x => F c x i))) := by
    rw [old_signed_primal_error_size_sq]
    simpa [F] using hseries.2
  have hfactor : 0 ≤ 1 - α ^ 2 := by
    have hα := Scalar.inverse_history_discount_range
    exact sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)
  rw [hVeq]
  calc
    _ ≤ (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * lemmaVInverseDepthMax Q a j *
        (descendantsAverage Q j (fun V => traceDefect (openCubeSet V) a 1) -
          traceDefect (openCubeSet Q) a 1) :=
      mul_le_mul_of_nonneg_left hcompare hfactor
    _ = rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j (fun V => traceDefect (openCubeSet V) a 1) -
          traceDefect (openCubeSet Q) a 1) := by
      unfold rawWeakTraceProxy
      rfl

private theorem mixed_bridge_local_paired_proxy
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedPrimalErrorSize Q Q nu sigma hnu hsigma k ^ 2 +
      oldSignedReciprocalErrorSize Q Q nu sigma hnu hsigma k ^ 2 ≤
      2 * rawWeakTraceProxy (lemmaVInverseDepthMax Q a)
        (fun j => descendantsAverage Q j
          (fun V => traceDefect (openCubeSet V) a 1)) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  simpa only [a] using old_signed_parent_paired_weak_bound Q nu sigma hnu hsigma k

private theorem mixed_bridge_local_theta_core_summable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (a : CoeffField 2) {lamA LamA : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (htrace : ∀ j : ℕ,
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
        rawWeakTraceSequence M m Q t ω j)
    (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      mixedOldDepthCoefficient M m t j ω *
        rawWeakTraceSequence M m Q t ω j) := by
  let α := Scalar.inverseHistoryDiscount
  let C : ℝ := 3683 / 2500
  let B : ℝ := mixedBridgeBstar M m t ω
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hT0 (j : ℕ) : 0 ≤ rawWeakTraceSequence M m Q t ω j :=
    raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  have hTsum : Summable (fun j : ℕ => α ^ j *
      rawWeakTraceSequence M m Q t ω j) := by
    have hs := old_signed_trace_depth_series_summable Q a hEllA
    apply hs.congr
    intro j
    rw [htrace j]
  have hB0 : 0 ≤ B := mixed_bridge_bstar_nonneg M m t ω
  have hR0 (j : ℕ) : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
    change 0 ≤ positiveSplitRemainder _ _ _
    exact (positive_split _ _ _).1
  have hCformula (j : ℕ) :=
    mixed_old_depth_coefficient_formula M m t j ω
  have hC0 (j : ℕ) : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
    rw [hCformula j]
    exact add_nonneg (mul_nonneg (by norm_num [C])
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) (hR0 j)
  have hexp : -(1 / 4 : ℝ) + 2 * M.gamma < 0 := by
    dsimp [gammaZero] at hγ ⊢
    norm_num at hγ ⊢
    linarith
  have hq : α * (3 : ℝ) ^ (2 * M.gamma) < 1 := by
    have heq : α * (3 : ℝ) ^ (2 * M.gamma) =
        (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
      dsimp [α, Scalar.inverseHistoryDiscount]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [heq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hbaseq : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) ≤ α := by
    have hmul : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) =
        α * (α * (3 : ℝ) ^ (2 * M.gamma)) := by ring
    rw [hmul]
    calc
      α * (α * (3 : ℝ) ^ (2 * M.gamma)) ≤ α * 1 :=
        mul_le_mul_of_nonneg_left hq.le hα0
      _ = α := by ring
  have hpow (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ α ^ j := by
    have hpow3 : (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
        ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ = (α ^ 2 * (3 : ℝ) ^ (2 * M.gamma)) ^ j := by
        rw [pow_mul, hpow3, ← mul_pow]
      _ ≤ α ^ j := pow_le_pow_left₀
        (mul_nonneg (sq_nonneg α)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) hbaseq j
  have hbaseline (j : ℕ) :
      α ^ (2 * j) * (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ≤ C * α ^ j := by
    have hC : 0 ≤ C := by norm_num [C]
    calc
      _ = C * (α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by ring
      _ ≤ C * α ^ j := mul_le_mul_of_nonneg_left (hpow j) hC
  have hRdiscount (j : ℕ) :
      α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω ≤ B * α ^ j := by
    have hR := mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
    calc
      _ = α ^ j * (α ^ j * mixedOldLocalDepthRemainder M m t j ω) := by
        rw [show 2 * j = j + j by omega, pow_add]
        ring
      _ ≤ α ^ j * B := mul_le_mul_of_nonneg_left hR (pow_nonneg hα0 j)
      _ = B * α ^ j := by ring
  have hmajorant : Summable (fun j : ℕ => (C + B) *
      (α ^ j * rawWeakTraceSequence M m Q t ω j)) :=
    hTsum.mul_left (C + B)
  apply Summable.of_nonneg_of_le
  · intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hC0 j)) (hT0 j)
  · intro j
    have hcoef : α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω ≤
        (C + B) * α ^ j := by
      rw [hCformula j]
      calc
        α ^ (2 * j) *
            (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) +
              mixedOldLocalDepthRemainder M m t j ω) ≤
            C * α ^ j + B * α ^ j := by
          calc
            _ = α ^ (2 * j) *
                (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) +
                  α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω := by ring
            _ ≤ C * α ^ j + B * α ^ j := add_le_add (hbaseline j) (hRdiscount j)
        _ = (C + B) * α ^ j := by ring
    calc
      α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω *
          rawWeakTraceSequence M m Q t ω j ≤
        ((C + B) * α ^ j) * rawWeakTraceSequence M m Q t ω j :=
          mul_le_mul_of_nonneg_right hcoef (hT0 j)
      _ = (C + B) *
          (α ^ j * rawWeakTraceSequence M m Q t ω j) := by ring
  · exact hmajorant

private theorem mixed_bridge_local_coefficient_summable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (ω : Cutoff.CutoffSample 2) (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      mixedOldDepthCoefficient M m t j ω) := by
  let α := Scalar.inverseHistoryDiscount
  let C : ℝ := 3683 / 2500
  let B : ℝ := mixedBridgeBstar M m t ω
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hαsum : Summable (fun j : ℕ => α ^ j) :=
    summable_geometric_of_lt_one hα0 hα.2
  have hB0 : 0 ≤ B := mixed_bridge_bstar_nonneg M m t ω
  have hexp : -(1 / 4 : ℝ) + 2 * M.gamma < 0 := by
    dsimp [gammaZero] at hγ ⊢
    norm_num at hγ ⊢
    linarith
  have hq : α * (3 : ℝ) ^ (2 * M.gamma) < 1 := by
    have heq : α * (3 : ℝ) ^ (2 * M.gamma) =
        (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
      dsimp [α, Scalar.inverseHistoryDiscount]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [heq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hbaseq : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) ≤ α := by
    have hmul : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) =
        α * (α * (3 : ℝ) ^ (2 * M.gamma)) := by ring
    rw [hmul]
    calc
      α * (α * (3 : ℝ) ^ (2 * M.gamma)) ≤ α * 1 :=
        mul_le_mul_of_nonneg_left hq.le hα0
      _ = α := by ring
  have hpow (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ α ^ j := by
    have hpow3 : (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
        ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ = (α ^ 2 * (3 : ℝ) ^ (2 * M.gamma)) ^ j := by
        rw [pow_mul, hpow3, ← mul_pow]
      _ ≤ α ^ j := pow_le_pow_left₀
        (mul_nonneg (sq_nonneg α)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) hbaseq j
  have hcoef (j : ℕ) :
      α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω ≤
        (C + B) * α ^ j := by
    rw [mixed_old_depth_coefficient_formula]
    calc
      α ^ (2 * j) *
          (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) +
            mixedOldLocalDepthRemainder M m t j ω) ≤
          C * α ^ j + B * α ^ j := by
        have hbase : α ^ (2 * j) *
            (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ≤ C * α ^ j := by
          have hC : 0 ≤ C := by norm_num [C]
          calc
            _ = C * (α ^ (2 * j) *
                (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by ring
            _ ≤ C * α ^ j := mul_le_mul_of_nonneg_left (hpow j) hC
        have hR := mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
        have hR' : α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω ≤
            B * α ^ j := by
          calc
            _ = α ^ j * (α ^ j * mixedOldLocalDepthRemainder M m t j ω) := by
              rw [show 2 * j = j + j by omega, pow_add]
              ring
            _ ≤ α ^ j * B := mul_le_mul_of_nonneg_left hR (pow_nonneg hα0 j)
            _ = B * α ^ j := by ring
        calc
          _ = α ^ (2 * j) *
              (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) +
                α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω := by ring
          _ ≤ C * α ^ j + B * α ^ j := add_le_add hbase hR'
      _ = (C + B) * α ^ j := by ring
  apply Summable.of_nonneg_of_le
  · intro j
    rw [mixed_old_depth_coefficient_formula]
    exact mul_nonneg (pow_nonneg hα0 _)
      (add_nonneg (mul_nonneg (by norm_num [C])
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) (by
          change 0 ≤ positiveSplitRemainder _ _ _
          exact (positive_split _ _ _).1))
  · intro j
    exact hcoef j
  · exact hαsum.mul_left (C + B)

private theorem mixed_bridge_local_parent_canonical_cell_residual_eq
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedCellResidual Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) =ᵐ[
        volumeMeasureOn (openCubeSet U)]
      oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P := by
  let kU := oldSignedCellCoefficient Q U hU k
  let F := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  let hF : MemBlockL2 (openCubeSet Q) F := Lp.memLp F
  let hFU : MemBlockL2 (openCubeSet U) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hU)
  let X : HilbertBlockL2 (openCubeSet U) := toHilbertBlockL2OfBlockField hFU
  let D := scalarFrameEnergyData U nu sigma hnu hsigma kU
  let K := scalarFrameVariationSpace U nu sigma hnu hsigma kU
  have hXfield : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn (openCubeSet U)] F := by
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField hFU]
    exact coeFn_toBlockL2 hFU
  have hparent : scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) = F := by
    rw [old_signed_affine_residual_field]
    rfl
  have hproj : K.toSubmodule.starProjection (responseEnergyUp D X) = 0 := by
    apply K.toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact K.toSubmodule.zero_mem
    · intro Y hY
      let hYmem : Y.down ∈
          (scalarFrameRealization U nu sigma hnu hsigma kU).correctionSpace.correctionSpace := hY
      let Yfield := hilbertBlockL2ToBlockL2 Y.down
      have hYvariation : ScalarVariation (openCubeSet U) Yfield :=
        old_signed_hilbert_correction_variation U nu sigma hnu hsigma kU
          Y.down hYmem
      have hYfield : MemBlockL2 (openCubeSet U) Yfield := Yfield.property
      have hYrebuild : toHilbertBlockL2OfBlockField hYfield = Y.down :=
        hilbert_field_rebuild _
      have horth := scalar_residual_local_orthogonal Q U hU nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)
        Yfield hYvariation
      have hcoeff := old_signed_cell_frame_coefficient_ae Q U hU nu sigma k
      have havg : volumeAverage (openCubeSet U) (fun x =>
          blockVecDot (Yfield x)
            (blockMatVecMul (blockCoeffField
              (responseFramePlanarCoefficientField nu sigma kU) x) (F x))) =
          volumeAverage (openCubeSet U) (fun x =>
          blockVecDot (Yfield x)
            (blockMatVecMul (blockCoeffField
              (responseFramePlanarCoefficientField nu sigma k) x)
              ((scalarResidualField Q nu sigma hnu hsigma k
                ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x))) := by
        unfold volumeAverage
        congr 1
        apply integral_congr_ae
        filter_upwards [hcoeff] with x hax
        have hax' : responseFramePlanarCoefficientField nu sigma kU x =
            responseFramePlanarCoefficientField nu sigma k x := by
          simpa [kU] using hax
        have haxBlock : blockCoeffField (responseFramePlanarCoefficientField nu sigma kU) x =
            blockCoeffField (responseFramePlanarCoefficientField nu sigma k) x := by
          simpa [blockCoeffField] using congrArg blockMatrixOfCoeff hax'
        have hparentx :
            (scalarResidualField Q nu sigma hnu hsigma k
              ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x = F x :=
          congrArg (fun f : BlockL2 (openCubeSet Q) => f x) hparent
        rw [haxBlock, ← hparentx]
      have hbil := scalar_frame_bilinear_field U nu sigma hnu hsigma kU hFU hYfield
      rw [hYrebuild] at hbil
      rw [sub_zero]
      change (scalarFrameRealization U nu sigma hnu hsigma kU).energyBilin X Y.down = 0
      rw [hbil]
      exact havg.trans horth
  have hres : scalarProjectionResidual U nu sigma hnu hsigma kU X = X := by
    change (responseEnergyUp D X -
      K.toSubmodule.starProjection (responseEnergyUp D X)).down = X
    rw [hproj]
    simp [responseEnergyUp_down]
  change hilbertBlockL2ToBlockL2
    (scalarProjectionResidual U nu sigma hnu hsigma kU X) =ᵐ[
      volumeMeasureOn (openCubeSet U)] F
  rw [hres]
  exact hXfield

private theorem mixed_bridge_local_first_corrector_grad_zero
    (Q U : TriadicCube 2) (hU : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (oldSignedCellFirstCorrector Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P))).toH1Function.grad =ᵐ[
        volumeMeasureOn (openCubeSet U)] 0 := by
  rw [old_signed_cell_first_corrector_grad]
  have hres := mixed_bridge_local_parent_canonical_cell_residual_eq
    Q U hU nu sigma hnu hsigma k P
  filter_upwards [hres] with x hx
  have hfirst :
      (oldSignedCellResidual Q U hU nu sigma hnu hsigma k
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
        (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) x).1 =
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 :=
    congrArg Prod.fst hx
  change (oldSignedCellResidual Q U hU nu sigma hnu hsigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)
      (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P)) x).1 -
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 = 0
  exact sub_eq_zero.mpr hfirst

private theorem mixed_bridge_local_vectorWeakHaarNorm_zero
    (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : F =ᵐ[volumeMeasureOn (openCubeSet Q)] 0) :
    vectorWeakHaarNorm Q F = 0 := by
  have hF' : F =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact hF
  have hcoord (i : Fin 2) : (fun x => F x i) =ᵐ[volume.restrict (cubeSet Q)] 0 := by
    filter_upwards [hF'] with x hx
    exact congrArg (fun v : Vec 2 => v i) hx
  have hzeroProj (j : ℕ) : cubeProjection Q j (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
    funext x
    simp [cubeProjection, cubeAverage_const]
  unfold vectorWeakHaarNorm
  have hEnergy : vectorWeakHaarEnergy Q F =
      vectorWeakHaarEnergy Q (fun _ : Vec 2 => (0 : Vec 2)) := by
    unfold vectorWeakHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    unfold dualEnergy
    exact diagPrimalEnergy_congr_ae Q (Real.sqrt 3)⁻¹ (hcoord i)
  rw [hEnergy]
  simp [vectorWeakHaarEnergy, dualEnergy, primalEnergy, energy, pairing,
    cubeIncrement_zero, cubeIncrement_succ, hzeroProj, cubeAverage_const]

private theorem mixed_bridge_local_corrector_square_zero'
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) (V : SquareCells U j) :
    mixedBridgeLocalCorrectorSq' M m U t ω j V = 0 := by
  classical
  unfold mixedBridgeLocalCorrectorSq'
  apply Finset.sum_eq_zero
  intro a ha
  have hV : openCubeSet V.val ⊆ openCubeSet U :=
    openCubeSet_subset_of_mem_descendantsAtDepth V.property
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k := mainAffineOpenResponseRestriction U
    (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  have hgrad := mixed_bridge_local_first_corrector_grad_zero
    U V.val hV M.nu σ M.nu_pos hσ k (blockBasis a)
  rw [mixed_bridge_local_vectorWeakHaarNorm_zero V.val hgrad]
  simp

private theorem mixed_bridge_local_depth_square_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    mixedBridgeVLocalDepthSq' M m U t ω j = 0 := by
  classical
  unfold mixedBridgeVLocalDepthSq' Cold.squareCellMean
  have hsum : ∑ V : SquareCells U j,
      mixedBridgeLocalCorrectorSq' M m U t ω j V = 0 := by
    apply Finset.sum_eq_zero
    intro V hV
    exact mixed_bridge_local_corrector_square_zero' M m U t ω j V
  rw [hsum]
  simp

private theorem mixed_bridge_local_vl2_zero
    (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    mixedBridgeVl2Local M m U t ω = 0 := by
  unfold mixedBridgeVl2Local
  have hz (j : ℕ) : mixedBridgeVLocalDepthSq' M m U t ω j = 0 :=
    mixed_bridge_local_depth_square_zero M m U t ω j
  simp_rw [hz]
  simp

private theorem mixed_bridge_local_pointwise_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mixedBridgeVLocal M m U t ω ^ 2 ≤
        mixedOldTheta M m U t ω - mainBetaOld * rawCubeFourLoadTrace M m U t ω ∧
      mixedBridgeVLocal M m U t ω ^ 2 + mixedBridgeGLocal M m U t ω ^ 2 ≤
        2 * mixedOldTheta M m U t ω := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let α := Scalar.inverseHistoryDiscount
  let σ : ℝ := Annealed.sigmaBar M m
  let k (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet U) :=
    mainAffineOpenResponseRestriction U
      (Gaussian.modelInsertedScalar (closure (cubeSet U)) m t ω)
  let a (ω : Cutoff.CutoffSample 2) : CoeffField 2 :=
    responseFramePlanarCoefficientField M.nu σ (k ω)
  let C (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
    mixedOldDepthCoefficient M m t j ω
  let D (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
    lemmaVInverseDepthMax U (a ω) j
  let T (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
    rawWeakTraceSequence M m U t ω j
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hEll (ω : Cutoff.CutoffSample 2) :
      IsEllipticFieldOn (M.nu / σ)
        (((M.nu / σ) ^ 2 + (‖k ω‖ / σ) ^ 2) / (M.nu / σ))
        (openCubeSet U) (a ω) := by
    exact responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U) M.nu σ M.nu_pos hσ (k ω)
  have htrace (ω : Cutoff.CutoffSample 2) (j : ℕ) :
      descendantsAverage U j (fun V => traceDefect (openCubeSet V) (a ω) 1) = T j ω := by
    simpa [T, a, k, σ] using
      mixed_bridge_local_trace_average_eq M m t ht U ω j
  have hparentTrace (ω : Cutoff.CutoffSample 2) :
      traceDefect (openCubeSet U) (a ω) 1 = rawCubeFourLoadTrace M m U t ω := by
    have h0 := htrace ω 0
    have hAvg : descendantsAverage U 0
        (fun V => traceDefect (openCubeSet V) (a ω) 1) =
          traceDefect (openCubeSet U) (a ω) 1 := by
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    have hTzero : T 0 ω = rawCubeFourLoadTrace M m U t ω := by
      change Cold.squareCellMean U 0
        (fun C => rawCubeFourLoadTrace M m C.1 t ω) = _
      rw [mixed_bridge_local_squareCellMean_eq_descendantsAverage U 0
        (fun V => rawCubeFourLoadTrace M m V t ω)]
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    rw [hAvg, hTzero] at h0
    exact h0
  have hdepth (j : ℕ) : ∀ᵐ ω ∂μ, D j ω ≤ C j ω := by
    simpa only [D, C, a, k, σ, μ] using
      mixed_bridge_local_depth_inverse_max_bound
        M h hM hγ N hpast m hm t ht U hU j
  have hdepthAll : ∀ᵐ ω ∂μ, ∀ j : ℕ, D j ω ≤ C j ω := by
    apply ae_all_iff.mpr
    intro j
    exact hdepth j
  have hθSum (ω : CutoffSample 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * C j ω * T j ω) := by
    have hEllω := hEll ω
    have htraceω (j : ℕ) := htrace ω j
    simpa [C, T, α] using mixed_bridge_local_theta_core_summable
      M m t ht ω U (a ω) hEllω htraceω hγ
  have hθSumRight (ω : CutoffSample 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * (C j ω * T j ω)) := by
    simpa only [← mul_assoc] using hθSum ω
  have hCoeffSum (ω : CutoffSample 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * C j ω) := by
    simpa [C, α] using mixed_bridge_local_coefficient_summable
      M m t ht ω hγ
  have hq0 : 0 ≤ α ^ 2 := sq_nonneg α
  have hq1 : α ^ 2 < 1 := by
    nlinarith [Scalar.inverse_history_discount_range.1,
      Scalar.inverse_history_discount_range.2]
  have hWsum : Summable (fun j : ℕ => (1 - α ^ 2) * α ^ (2 * j)) := by
    have hα := Scalar.inverse_history_discount_range
    have hgeom := summable_geometric_of_lt_one hq0 hq1
    have hh := hgeom.mul_left (1 - α ^ 2)
    apply hh.congr
    intro j
    simp [pow_mul]
  have hWtotal : ∑' j : ℕ, (1 - α ^ 2) * α ^ (2 * j) = 1 := by
    let q : ℝ := α ^ 2
    have hq0 : 0 ≤ q := sq_nonneg α
    have hq1 : q < 1 := by
      dsimp [q]
      nlinarith [Scalar.inverse_history_discount_range.1,
        Scalar.inverse_history_discount_range.2]
    have hsum : ∑' j : ℕ, q ^ j = (1 - q)⁻¹ :=
      tsum_geometric_of_lt_one hq0 hq1
    calc
      _ = ∑' j : ℕ, (1 - q) * q ^ j := by
        apply tsum_congr
        intro j
        simp [q, pow_mul]
      _ = (1 - q) * ∑' j : ℕ, q ^ j := tsum_mul_left
      _ = 1 := by rw [hsum]; exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hq1))
  have hCnonneg (j : ℕ) (ω : CutoffSample 2) : 0 ≤ C j ω := by
    rw [show C j ω = mixedOldDepthCoefficient M m t j ω by rfl,
      mixed_old_depth_coefficient_formula]
    change 0 ≤ (3683 / 2500 : ℝ) * (3 : ℝ) ^
      (2 * M.gamma * (j : ℝ)) + positiveSplitRemainder _ _ _
    exact add_nonneg (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (by norm_num) _)) ((positive_split _ _ _).1)
  have hCminor (j : ℕ) (ω : CutoffSample 2) : mainBetaOld ≤ C j ω := by
    rw [show C j ω = mixedOldDepthCoefficient M m t j ω by rfl,
      mixed_old_depth_coefficient_formula]
    have hpow : 1 ≤ (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity [M.shellPrefix.gamma_pos])
    have hR : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
      change 0 ≤ positiveSplitRemainder _ _ _
      exact (positive_split _ _ _).1
    dsimp [mainBetaOld]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3683 / 2500)]
  have hWcoeffSum (ω : CutoffSample 2) :
      Summable (fun j : ℕ => ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) := by
    have hh := (hCoeffSum ω).mul_left (1 - α ^ 2)
    apply hh.congr
    intro j
    ring
  have hmassLower (ω : CutoffSample 2) :
      mainBetaOld ≤ ∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω := by
    have hbaseSum : Summable (fun j : ℕ =>
        ((1 - α ^ 2) * α ^ (2 * j)) * mainBetaOld) := hWsum.mul_right mainBetaOld
    have hterm (j : ℕ) :
        ((1 - α ^ 2) * α ^ (2 * j)) * mainBetaOld ≤
          ((1 - α ^ 2) * α ^ (2 * j)) * C j ω :=
      mul_le_mul_of_nonneg_left (hCminor j ω)
        (mul_nonneg (sub_nonneg.mpr (pow_le_one₀
          Scalar.inverse_history_discount_range.1.le
          Scalar.inverse_history_discount_range.2.le))
          (pow_nonneg Scalar.inverse_history_discount_range.1.le _))
    have hsum := hbaseSum.tsum_le_tsum hterm (hWcoeffSum ω)
    have hbaseValue : ∑' j : ℕ,
        ((1 - α ^ 2) * α ^ (2 * j)) * mainBetaOld = mainBetaOld := by
      calc
        _ = mainBetaOld * ∑' j : ℕ, (1 - α ^ 2) * α ^ (2 * j) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro j
          ring
        _ = mainBetaOld := by rw [hWtotal]; ring
    rw [hbaseValue] at hsum
    exact hsum
  have hmassEq (ω : CutoffSample 2) :
      (∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) =
        (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * C j ω := by
    calc
      _ = ∑' j : ℕ, (1 - α ^ 2) * (α ^ (2 * j) * C j ω) := by
        apply tsum_congr
        intro j
        ring
      _ = _ := tsum_mul_left
  have hthetaEq (ω : CutoffSample 2) :
      mixedOldTheta M m U t ω =
        rawWeakTraceProxy (fun j => C j ω) (fun j => T j ω) := by
    unfold mixedOldTheta rawWeakTraceProxy
    calc
      _ = ∑' j : ℕ, (1 - α ^ 2) *
          (α ^ (2 * j) * C j ω * T j ω) := by
        apply tsum_congr
        intro j
        simp [mixedOldThetaTerm, mixedDepthTraceAverage, C, T]
        ring
      _ = _ := tsum_mul_left
  have hgap0 (j : ℕ) (ω : CutoffSample 2) :
      0 ≤ T j ω - rawCubeFourLoadTrace M m U t ω := by
    have hparent := old_signed_parent_trace_le_child U j M.nu σ M.nu_pos hσ (k ω)
    have hparent' : rawCubeFourLoadTrace M m U t ω ≤ T j ω := by
      rw [← hparentTrace ω, ← htrace ω j]
      exact hparent
    exact sub_nonneg.mpr hparent'
  have hgapLeT (j : ℕ) (ω : CutoffSample 2) :
      T j ω - rawCubeFourLoadTrace M m U t ω ≤ T j ω := by
    exact sub_le_self _ (raw_cube_four_load_trace_nonneg M m U t
      ⟨ht.1, ht.2⟩ ω)
  have hdepthRaw : ∀ᵐ ω ∂μ, ∀ j : ℕ, D j ω ≤ C j ω := hdepthAll
  filter_upwards [hdepthRaw] with ω hD
  have hT0 (j : ℕ) : 0 ≤ T j ω := by
    exact raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j
  have hgapSeries : Summable (fun j : ℕ =>
      α ^ (2 * j) * C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω)) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
        (hCnonneg j ω)) (hgap0 j ω)
    · intro j
      have hterm : C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) ≤ C j ω * T j ω :=
        mul_le_mul_of_nonneg_left (hgapLeT j ω) (hCnonneg j ω)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    · exact hθSumRight ω
  have hgapSeriesRight : Summable (fun j : ℕ =>
      α ^ (2 * j) * (C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω))) := by
    simpa only [← mul_assoc] using hgapSeries
  have hgapProxyCompare :
      rawWeakTraceProxy (fun j => D j ω)
        (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) ≤
      rawWeakTraceProxy (fun j => C j ω)
        (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) := by
    unfold rawWeakTraceProxy
    apply mul_le_mul_of_nonneg_left _
      (sub_nonneg.mpr (pow_le_one₀ Scalar.inverse_history_discount_range.1.le
        Scalar.inverse_history_discount_range.2.le))
    have hDgapSeries : Summable (fun j : ℕ =>
        α ^ (2 * j) * D j ω *
          (T j ω - rawCubeFourLoadTrace M m U t ω)) := by
      apply Summable.of_nonneg_of_le
      · intro j
        exact mul_nonneg (mul_nonneg
          (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
          (lemmaVInverseDepthMax_nonneg U (a ω) j))
          (hgap0 j ω)
      · intro j
        have hterm : D j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) ≤
            C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) :=
          mul_le_mul_of_nonneg_right (hD j) (hgap0 j ω)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm
          (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
      · simpa only [mul_assoc] using hgapSeries
    have hterm (j : ℕ) : α ^ (2 * j) * D j ω *
        (T j ω - rawCubeFourLoadTrace M m U t ω) ≤
          α ^ (2 * j) * C j ω *
            (T j ω - rawCubeFourLoadTrace M m U t ω) := by
      have hterm : D j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) ≤
          C j ω * (T j ω - rawCubeFourLoadTrace M m U t ω) :=
        mul_le_mul_of_nonneg_right (hD j) (hgap0 j ω)
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hterm
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    exact hDgapSeries.tsum_le_tsum hterm hgapSeries
  have hpairSeries : Summable (fun j : ℕ => α ^ (2 * j) * D j ω * T j ω) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg (mul_nonneg (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
        (lemmaVInverseDepthMax_nonneg U (a ω) j)) (hT0 j)
    · intro j
      simpa only [← mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hD j) (hT0 j))
        (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    · exact hθSum ω
  have hpairProxyCompare :
      rawWeakTraceProxy (fun j => D j ω) (fun j => T j ω) ≤
      rawWeakTraceProxy (fun j => C j ω) (fun j => T j ω) := by
    unfold rawWeakTraceProxy
    apply mul_le_mul_of_nonneg_left _
      (sub_nonneg.mpr (pow_le_one₀ Scalar.inverse_history_discount_range.1.le
        Scalar.inverse_history_discount_range.2.le))
    have hterm (j : ℕ) : α ^ (2 * j) * D j ω * T j ω ≤
        α ^ (2 * j) * C j ω * T j ω := by
      simpa only [← mul_assoc] using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hD j) (hT0 j))
          (pow_nonneg Scalar.inverse_history_discount_range.1.le (2 * j))
    exact hpairSeries.tsum_le_tsum hterm (hθSum ω)
  have hcoefLower := hmassLower ω
  have hgapMassEq :
      rawWeakTraceProxy (fun j => C j ω)
        (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) =
      mixedOldTheta M m U t ω - rawCubeFourLoadTrace M m U t ω *
        (∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) := by
    have hCoeffTimesF := (hCoeffSum ω).mul_left
      (rawCubeFourLoadTrace M m U t ω)
    have hsumGap :
        (∑' j : ℕ, α ^ (2 * j) * C j ω *
          (T j ω - rawCubeFourLoadTrace M m U t ω)) =
          (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            rawCubeFourLoadTrace M m U t ω *
              (∑' j : ℕ, α ^ (2 * j) * C j ω) := by
      calc
        _ = ∑' j : ℕ,
            (α ^ (2 * j) * C j ω * T j ω -
              rawCubeFourLoadTrace M m U t ω * (α ^ (2 * j) * C j ω)) := by
          apply tsum_congr
          intro j
          ring
        _ = (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            (∑' j : ℕ, rawCubeFourLoadTrace M m U t ω *
              (α ^ (2 * j) * C j ω)) := (hθSum ω).tsum_sub hCoeffTimesF
        _ = (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            rawCubeFourLoadTrace M m U t ω *
              (∑' j : ℕ, α ^ (2 * j) * C j ω) := by
          rw [tsum_mul_left]
    calc
      _ = (1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * C j ω *
            (T j ω - rawCubeFourLoadTrace M m U t ω)) := by
        rfl
      _ = (1 - α ^ 2) *
          ((∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
            rawCubeFourLoadTrace M m U t ω *
              (∑' j : ℕ, α ^ (2 * j) * C j ω)) := by rw [hsumGap]
      _ = (1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω) -
          rawCubeFourLoadTrace M m U t ω *
            ((1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * C j ω) := by ring
      _ = mixedOldTheta M m U t ω - rawCubeFourLoadTrace M m U t ω *
          (∑' j : ℕ, ((1 - α ^ 2) * α ^ (2 * j)) * C j ω) := by
        have hthetaValue : mixedOldTheta M m U t ω =
            (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * C j ω * T j ω := by
          simpa [rawWeakTraceProxy] using hthetaEq ω
        rw [← hthetaValue, ← hmassEq ω]
  have hVgap := mixed_bridge_local_primal_gap_proxy U M.nu σ M.nu_pos hσ (k ω)
  have hVpair := mixed_bridge_local_paired_proxy U M.nu σ M.nu_pos hσ (k ω)
  constructor
  · calc
      mixedBridgeVLocal M m U t ω ^ 2 ≤
          rawWeakTraceProxy (fun j => D j ω)
            (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) := by
              simpa only [mixedBridgeVLocal, D, T, a, k, σ,
                htrace ω, hparentTrace ω] using hVgap
      _ ≤ rawWeakTraceProxy (fun j => C j ω)
            (fun j => T j ω - rawCubeFourLoadTrace M m U t ω) := hgapProxyCompare
      _ ≤ mixedOldTheta M m U t ω - mainBetaOld *
            rawCubeFourLoadTrace M m U t ω := by
        rw [hgapMassEq]
        have hmass := mul_le_mul_of_nonneg_right hcoefLower
          (raw_cube_four_load_trace_nonneg M m U t ⟨ht.1, ht.2⟩ ω)
        nlinarith [hmass]
  · calc
      mixedBridgeVLocal M m U t ω ^ 2 + mixedBridgeGLocal M m U t ω ^ 2 ≤
          2 * rawWeakTraceProxy (fun j => D j ω) (fun j => T j ω) := by
            simpa only [mixedBridgeVLocal, mixedBridgeGLocal, D, T, a, k, σ,
              htrace ω] using hVpair
      _ ≤ 2 * rawWeakTraceProxy (fun j => C j ω) (fun j => T j ω) :=
        mul_le_mul_of_nonneg_left hpairProxyCompare (by norm_num)
      _ = 2 * mixedOldTheta M m U t ω := by rw [hthetaEq ω]

/-- Local parent-gap rows on each depth-five source cell.  The OLD frame stays
at the insertion label `m`; the inverse envelope is the explicit `mainChi`
envelope, and the local first-corrector carrier is its actual zero series. -/
theorem mixed_bridge_local_parent_gap_rows
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 m) 5) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
    let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
    let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
    let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
    let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ
    Integrable (fun ω => V ω ^ 2) μ ∧
    (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U ∧
    (∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi) ∧
    Integrable (fun ω => B ω * G ω ^ 2) μ ∧
    (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi ∧
    Integrable (fun ω => B ω * Vl ω ^ 2) μ ∧
    (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
      mainBeta * xi + mainEpsNew * mainD * mainBeta *
        mainEnvelopeH (theta M) M.gamma t := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2
  let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
  let B : Cutoff.CutoffSample 2 → ℝ := mixedGlobalHistoryMax M m t
  let V : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVLocal M m U t
  let G : Cutoff.CutoffSample 2 → ℝ := mixedBridgeGLocal M m U t
  let Vl : Cutoff.CutoffSample 2 → ℝ := mixedBridgeVlLocal M m U t
  let f_U := ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ

  have hEnvelope := main_envelope_xi_depth5_actual_law
    M h hM hγ N hpast m hm t ht U hU
  have hThetaInt : Integrable (mixedOldTheta M m U t) μ := by
    simpa [μ] using (hEnvelope ⟨0, by norm_num⟩).1
  have hBcarrier (ω : Cutoff.CutoffSample 2) :
      B ω = mixedBridgeBstar M m t ω := by
    dsimp [B, mixedGlobalHistoryMax, mixedObserverRoots,
      mixedBridgeBstar]
    rw [← mixed_bridge_observer_roots_eq_bank_union m,
      ← mixed_bridge_bstar_eq_bank_finite_history M m t ht ω]
    exact ENNReal.toReal_ofReal
      (mixed_bridge_bstar_nonneg M m t ω)
  have hBmeas : Measurable B := by
    have heq : B = mixedBridgeBstar M m t := funext hBcarrier
    rw [heq]
    exact parent_gap_bstar_measurable M m t
  have hBnonneg (ω : Cutoff.CutoffSample 2) : 0 ≤ B ω := by
    rw [hBcarrier ω]
    exact mixed_bridge_bstar_nonneg M m t ω
  have hVmeas : Measurable (fun ω => V ω ^ 2) := by
    simpa [V] using mixed_bridge_local_v2_measurable M m U t
  have hGmeas : Measurable (fun ω => G ω ^ 2) := by
    simpa [G] using mixed_bridge_local_measurable M m U t
  have hThetaNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ mixedOldTheta M m U t ω := by
    unfold mixedOldTheta
    apply tsum_nonneg
    intro j
    rw [mixedOldThetaTerm]
    have hcoeff : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
      rw [mixed_old_depth_coefficient_formula]
      change 0 ≤ (3683 / 2500 : ℝ) * (3 : ℝ) ^
        (2 * M.gamma * (j : ℝ)) + positiveSplitRemainder _ _ _
      exact add_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by norm_num) _)) ((positive_split _ _ _).1)
    have hw : 0 ≤ (1 - Scalar.inverseHistoryDiscount ^ 2) *
        Scalar.inverseHistoryDiscount ^ (2 * j) :=
      mul_nonneg
        (sub_nonneg.mpr (pow_le_one₀
          Scalar.inverse_history_discount_range.1.le
          Scalar.inverse_history_discount_range.2.le))
        (pow_nonneg Scalar.inverse_history_discount_range.1.le _)
    exact mul_nonneg (mul_nonneg hw hcoeff)
      (raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j)
  have hXiNonneg : 0 ≤ xi := by
    have hpre : 0 ≤ mainSourceInversePrefix := by
      have hbeta : 0 < mainBetaOld / 100 := by norm_num [mainBetaOld]
      exact le_of_lt (lt_trans hbeta mainSourceInversePrefix_gate)
    exact hpre.trans (mainEnvelopeXi_ge_initial (sq_nonneg _)
      M.shellPrefix.gamma_pos.le hγ (ASDExplicitGamma.Cold.cold_theta_pos M).le ht.1)

  have hrows : ∀ᵐ ω ∂μ,
      V ω ^ 2 ≤ mixedOldTheta M m U t ω -
          mainBetaOld * rawCubeFourLoadTrace M m U t ω ∧
      V ω ^ 2 + G ω ^ 2 ≤ 2 * mixedOldTheta M m U t ω := by
    simpa [V, G, μ] using
      mixed_bridge_local_pointwise_rows M h hM hγ N hpast m hm t ht U hU
  have hTraceLaw := mixed_bridge_local_trace_mean
    M h hM hγ N hpast m hm t ht 5 le_rfl U hU 0
  have hTraceInt : Integrable (rawCubeFourLoadTrace M m U t) μ := by
    have hTInt := hTraceLaw.1
    have hEq (ω : Cutoff.CutoffSample 2) :
        mixedDepthTraceAverage M m U t ω 0 =
          rawCubeFourLoadTrace M m U t ω := by
      change Cold.squareCellMean U 0
        (fun C => rawCubeFourLoadTrace M m C.1 t ω) = _
      rw [mixed_bridge_local_squareCellMean_eq_descendantsAverage U 0
        (fun V => rawCubeFourLoadTrace M m V t ω)]
      simp [descendantsAverage, Homogenization.descendantsAtDepth_zero]
    exact hTInt.congr (Filter.Eventually.of_forall hEq)
  have hGapInt : Integrable
      (fun ω => mixedOldTheta M m U t ω -
        mainBetaOld * rawCubeFourLoadTrace M m U t ω) μ :=
    hThetaInt.sub (hTraceInt.const_mul mainBetaOld)
  have hVInt : Integrable (fun ω => V ω ^ 2) μ := by
    apply hGapInt.mono' hVmeas.aestronglyMeasurable
    filter_upwards [hrows] with ω hω
    have hleft : 0 ≤ V ω ^ 2 := sq_nonneg _
    have hright : 0 ≤ mixedOldTheta M m U t ω -
        mainBetaOld * rawCubeFourLoadTrace M m U t ω := le_trans hleft hω.1
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hω.1
  have hVIntegralBound :
      (∫ ω, V ω ^ 2 ∂μ) ≤ xi - mainBetaOld * f_U := by
    have hmono := integral_mono_ae hVInt hGapInt (by
      filter_upwards [hrows] with ω hω
      exact hω.1)
    have hthetaBound :
        (∫ ω, mixedOldTheta M m U t ω ∂μ) ≤ xi := by
      simpa [μ, xi, v] using (hEnvelope ⟨0, by norm_num⟩).2
    have hgapIntegral :
        (∫ ω, mixedOldTheta M m U t ω -
          mainBetaOld * rawCubeFourLoadTrace M m U t ω ∂μ) ≤
          xi - mainBetaOld * f_U := by
      rw [integral_sub hThetaInt (hTraceInt.const_mul mainBetaOld),
        integral_const_mul]
      exact sub_le_sub_right hthetaBound (mainBetaOld * f_U)
    exact hmono.trans hgapIntegral

  have hPairRows : ∀ k : Fin 4,
      Integrable (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ ∧
      (∫ ω, B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ∂μ) ≤
        2 * mainBeta ^ k.val * xi := by
    intro k
    have hEnv := hEnvelope k
    have hIntegrandMeas : Measurable
        (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) :=
      (hBmeas.pow_const k.val).mul (hVmeas.add hGmeas)
    have hpairInt : Integrable
        (fun ω => B ω ^ k.val * (V ω ^ 2 + G ω ^ 2)) μ := by
      apply (hEnv.1.const_mul 2).mono' hIntegrandMeas.aestronglyMeasurable
      filter_upwards [hrows] with ω hω
      have hpow : 0 ≤ B ω ^ k.val := pow_nonneg (hBnonneg ω) _
      have hleft : 0 ≤ B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) :=
        mul_nonneg hpow (add_nonneg (sq_nonneg _) (sq_nonneg _))
      have hright : 0 ≤ 2 * (B ω ^ k.val * mixedOldTheta M m U t ω) :=
        mul_nonneg (by norm_num) (mul_nonneg hpow (hThetaNonneg ω))
      have hbound : B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ≤
          2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := by
        calc
          _ ≤ B ω ^ k.val * (2 * mixedOldTheta M m U t ω) :=
            mul_le_mul_of_nonneg_left hω.2 hpow
          _ = _ := by ring
      rw [Real.norm_of_nonneg hleft]
      simpa [B] using hbound
    have hpairIntegral := integral_mono_ae hpairInt (hEnv.1.const_mul 2) (by
      filter_upwards [hrows] with ω hω
      have hpow : 0 ≤ B ω ^ k.val := pow_nonneg (hBnonneg ω) _
      calc
        B ω ^ k.val * (V ω ^ 2 + G ω ^ 2) ≤
            2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := by
              calc
                _ ≤ B ω ^ k.val * (2 * mixedOldTheta M m U t ω) :=
                  mul_le_mul_of_nonneg_left hω.2 hpow
                _ = _ := by ring
        _ = 2 * (B ω ^ k.val * mixedOldTheta M m U t ω) := rfl)
    have hEnvBound :
        (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) ≤
          mainBeta ^ k.val * xi := by
      simpa [B, μ, xi, v] using hEnv.2
    refine ⟨hpairInt, ?_⟩
    calc
      _ ≤ 2 * (∫ ω, B ω ^ k.val * mixedOldTheta M m U t ω ∂μ) := by
        simpa only [integral_const_mul] using hpairIntegral
      _ ≤ 2 * (mainBeta ^ k.val * xi) :=
        mul_le_mul_of_nonneg_left hEnvBound (by norm_num)
      _ = 2 * mainBeta ^ k.val * xi := by ring

  have hGInt : Integrable (fun ω => B ω * G ω ^ 2) μ := by
    have hmeas : Measurable (fun ω => B ω * G ω ^ 2) := hBmeas.mul hGmeas
    have hpair := hPairRows ⟨1, by norm_num⟩ |>.1
    apply hpair.mono' hmeas.aestronglyMeasurable
    filter_upwards with ω
    have hleft : 0 ≤ B ω * G ω ^ 2 := mul_nonneg (hBnonneg ω) (sq_nonneg _)
    have hright : 0 ≤ B ω ^ 1 * (V ω ^ 2 + G ω ^ 2) :=
      mul_nonneg (pow_nonneg (hBnonneg ω) 1)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hbound : B ω * G ω ^ 2 ≤ B ω ^ 1 * (V ω ^ 2 + G ω ^ 2) := by
      have hbase : G ω ^ 2 ≤ V ω ^ 2 + G ω ^ 2 := by nlinarith [sq_nonneg (V ω)]
      simpa only [pow_one] using mul_le_mul_of_nonneg_left hbase (hBnonneg ω)
    rw [Real.norm_of_nonneg hleft]
    simpa only [pow_one] using hbound
  have hGIntegralBound :
      (∫ ω, B ω * G ω ^ 2 ∂μ) ≤ 2 * mainBeta * xi := by
    have hmono := integral_mono_ae hGInt
      (hPairRows ⟨1, by norm_num⟩).1 (by
        filter_upwards with ω
        have hbase : G ω ^ 2 ≤ V ω ^ 2 + G ω ^ 2 := by nlinarith [sq_nonneg (V ω)]
        simpa only [pow_one] using mul_le_mul_of_nonneg_left hbase (hBnonneg ω))
    have hpairBound := (hPairRows ⟨1, by norm_num⟩).2
    simpa only [pow_one] using hmono.trans hpairBound

  have hVlZero (ω : CutoffSample 2) : Vl ω ^ 2 = 0 := by
    simp [Vl, mixedBridgeVlLocal, mixed_bridge_local_vl2_zero]
  have hVlInt : Integrable (fun ω => B ω * Vl ω ^ 2) μ := by
    have heq : (fun ω => B ω * Vl ω ^ 2) = fun _ : CutoffSample 2 => 0 := by
      funext ω
      rw [hVlZero ω]
      ring
    rw [heq]
    exact integrable_const 0
  have hVlIntegral : (∫ ω, B ω * Vl ω ^ 2 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with ω
    simp [hVlZero ω]
  have hVlBound :
      (∫ ω, B ω * Vl ω ^ 2 ∂μ) ≤
        mainBeta * xi + mainEpsNew * mainD * mainBeta *
          mainEnvelopeH (theta M) M.gamma t := by
    rw [hVlIntegral]
    have hβ : 0 ≤ mainBeta := by norm_num [mainBeta]
    have hε : 0 ≤ mainEpsNew := by norm_num [mainEpsNew]
    have hAlpha : 0 ≤ mainAlpha :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
    have hD : 0 ≤ mainD := by
      dsimp [mainD]
      exact add_nonneg (by norm_num) hAlpha
    have hH : 0 ≤ mainEnvelopeH (theta M) M.gamma t :=
      mainEnvelopeH_nonneg _ _ _
    positivity

  refine ⟨hVInt, hVIntegralBound, hPairRows, hGInt, hGIntegralBound,
    hVlInt, hVlBound⟩

end

end ASDExplicitGamma.Main
