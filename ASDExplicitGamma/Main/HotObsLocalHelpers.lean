module

public import ASDExplicitGamma.Main.HotObsEnvelope
public import ASDExplicitGamma.Main.MixedBridgeDepthFive
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit

/-! Observer-cell version of the local OLD parent-gap carriers (helpers). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Cold ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

noncomputable local instance mixedBridgeLocalBlockL2Measurable'
    (U : TriadicCube 2) : MeasurableSpace (BlockL2 (openCubeSet U)) := borel _

local instance mixedBridgeLocalBlockL2Borel'
    (U : TriadicCube 2) : BorelSpace (BlockL2 (openCubeSet U)) := ⟨rfl⟩

local instance mixedBridgeLocalBlockL2OpensMeasurable'
    (U : TriadicCube 2) : OpensMeasurableSpace (BlockL2 (openCubeSet U)) :=
  ⟨le_of_eq rfl⟩

local instance mixedBridgeLocalHilbertOpensMeasurable'
    (U : TriadicCube 2) : OpensMeasurableSpace (HilbertBlockL2 (openCubeSet U)) :=
  ⟨le_of_eq rfl⟩

local instance mixedBridgeLocalCubeCompact' (U : TriadicCube 2) :
    CompactSpace (closure (cubeSet U)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet U).isCompact_closure

theorem mixed_bridge_local_response_coefficient_measurable'
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

theorem mixed_bridge_local_canonical_field_measurable'
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
      (mixed_bridge_local_response_coefficient_measurable' U m t) F
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

theorem mixed_bridge_local_potentialCoordinate_ae'
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

theorem mixed_bridge_local_fluxCoordinate_ae'
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

theorem mixed_bridge_local_dualEnergy_congr_ae'
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

theorem mixed_bridge_local_primalEnergy_measurable'
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

theorem mixed_bridge_local_dualEnergy_measurable'
    {Ω : Type*} [MeasurableSpace Ω] (U : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure U))]
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure U)) (hu : Measurable u) :
    Measurable (fun ω => dualEnergy U (Real.sqrt 3) (fun x => u ω x)) := by
  unfold dualEnergy
  exact mixed_bridge_local_primalEnergy_measurable' U
    ((Real.sqrt 3)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg _)) u hu

theorem mixed_bridge_local_v2_measurable'
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
    mixed_bridge_local_response_coefficient_measurable' U m t
  have hcan (a : BlockCoord 2) : Measurable (can a) := by
    simpa [can, coeff, σ, hσ] using
      mixed_bridge_local_canonical_field_measurable' M m U t (blockBasis a)
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
    mixed_bridge_local_dualEnergy_measurable' U (u a i) (hu a i)
  have hcoordinateIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarNorm U (fun x => (can a ω x).1 - (blockBasis a).1) ^ 2 =
        ∑ i : Fin 2, dualEnergy U (Real.sqrt 3) (fun x => u a i ω x) := by
    rw [vectorWeakHaarNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    have hXeq : hilbertBlockL2ToBlockL2 (X a ω) = can a ω :=
      hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2 (can a ω)
    have hpot := mixed_bridge_local_potentialCoordinate_ae' U i (X a ω)
    have hpot' : hilbertVectorL2_normalizedCoordCLM U i
        (hilbertBlockL2PotentialCLM (X a ω)) =ᵐ[normalizedCubeMeasure U]
          fun x => (can a ω x).1 i := by
      rw [hXeq] at hpot
      exact hpot
    have hsub := mixed_bridge_local_dualEnergy_congr_ae' U
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

theorem mixed_bridge_local_measurable'
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
    mixed_bridge_local_response_coefficient_measurable' U m t
  have hcan (a : BlockCoord 2) : Measurable (can a) := by
    simpa [can, coeff, ν, σ, hν, hσ] using
      mixed_bridge_local_canonical_field_measurable' M m U t (blockBasis a)
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
    mixed_bridge_local_dualEnergy_measurable' U (u a i) (hu a i)
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
    have hFluxCoord := mixed_bridge_local_fluxCoordinate_ae' U i Tω
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
    have hde := mixed_bridge_local_dualEnergy_congr_ae' U hAE.symm
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

theorem mixed_bridge_bank_response_max_eq_finsetSup'
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

theorem mixed_bridge_local_depth_inverse_max_bound'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : Set.Icc (0 : ℝ) 1 t)
    (U : TriadicCube 2)
    (hUObserver : U ∈ bankObserverRoots (originCube 2 (m + 40)) 5)
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
    simpa only [f] using mixed_bridge_bank_response_max_eq_finsetSup'
      (descendantsAtDepth U j) hlocalNonempty M m (m + 40) weights ω
  have hunionSupEq : bankFiniteRootResponseMax D M m (m + 40) weights ω =
      ENNReal.ofReal (Book.Ch02.finsetSupReal D f) := by
    simpa only [f] using mixed_bridge_bank_response_max_eq_finsetSup'
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

theorem mixed_bridge_local_trace_cell_eq_raw'
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

theorem mixed_bridge_local_squareCellMean_eq_descendantsAverage'
    (Q : TriadicCube 2) (j : ℕ) (f : TriadicCube 2 → ℝ) :
    Cold.squareCellMean Q j (fun C => f C.1) = descendantsAverage Q j f := by
  unfold Cold.squareCellMean descendantsAverage
  congr 1
  exact Finset.sum_attach (descendantsAtDepth Q j) f

theorem mixed_bridge_local_trace_average_eq'
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
    mixed_bridge_local_trace_cell_eq_raw' M m t ht U ω a hframe j V hV
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
      exact (mixed_bridge_local_squareCellMean_eq_descendantsAverage' U j
        (fun V => rawCubeFourLoadTrace M m V t ω)).symm

theorem mixed_bridge_local_primal_gap_proxy'
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

theorem mixed_bridge_local_paired_proxy'
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

theorem mixed_bridge_local_theta_core_summable'
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

theorem mixed_bridge_local_coefficient_summable'
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

end

end ASDExplicitGamma.Main
