module

public import ASDExplicitGamma.Scalar.PhysicalCompressedResolvent
public import ASDExplicitGamma.Gaussian.AllOrderProjectedSource
public import ASDExplicitGamma.Main.FlatFieldH1Bounds
public import ASDExplicitGamma.Native.OldSignedFlatBlockFields
public import ASDExplicitGamma.Native.OldSignedAffineReciprocal
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Variational.LocalizedBlockSpace
public import ASDExplicitGamma.Variational.LocalizedEnergyBounds

/-! Physical old-resolvent carriers for the defect-source Wick estimate. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization Response MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped InnerProduct

noncomputable section

/-- The old constrained solution operator, expressed through the compressed
coercive operator. Its values are the actual zero-boundary
corrections in the old variational problem. -/
noncomputable def oldResolvent {U : Set (Vec 2)} {a : CoeffField 2}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : MuHilbertRealization U a) :
    HilbertBlockL2 U →L[ℝ] M.correctionSpace.correctionSpace.toSubmodule :=
  (compressed_variational_operator M).symm.toContinuousLinearMap.comp
    (Homogenization.subspaceRhs M.correctionSpace.correctionSpace M.energyBilin)

/-- The compressed inverse is the actual affine-correction solution operator
used by the old coefficient minimization. -/
theorem old_resolvent_eq_correctionMap {U : Set (Vec 2)} {a : CoeffField 2}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (M : MuHilbertRealization U a) (F : HilbertBlockL2 U) :
    oldResolvent M F = correctionMap M.correctionSpace.correctionSpace
      M.energyBilin M.energyCoercive F := by
  unfold oldResolvent compressed_variational_operator correctionMap
  rfl

/-- The actual fixed-frame insertion operator `C_H` on the response energy
carrier. This is the same shear used by the OLD constrained minimization. -/
noncomputable def oldInsertion {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U)
    (H : ResponseCoefficient U) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) →L[ℝ]
      EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H

/-- The OLD first response `u₁(H)=R_old C_H u₀` to one affine load, embedded
back into the fixed response-energy carrier. -/
noncomputable def oldFirstResponse {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) (H : ResponseCoefficient U) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) := by
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let u₀ := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  exact responseEnergyUp D
    (oldResolvent M ((oldInsertion hU hvol ν σ hν hσ k H u₀).down))

/-- The first block of the actual OLD first response has its genuine global
H10 potential, recovered from membership in the closed variational correction
space. -/
theorem old_first_response_zero_trace_potential (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (H : ResponseCoefficient (openCubeSet Q)) :
    IsPotentialZeroTraceOn (openCubeSet Q)
      (fun x => (hilbertBlockL2ToBlockL2
        (oldFirstResponse (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k P H).down x).1) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let S := oldFirstResponse hU hvol ν σ hν hσ k P H
  have hmem : (S.down : HilbertBlockL2 (openCubeSet Q)) ∈
      M.correctionSpace.correctionSpace := by
    change (oldResolvent M
      ((oldInsertion hU hvol ν σ hν hσ k H
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)).down) :
        HilbertBlockL2 (openCubeSet Q)) ∈ M.correctionSpace.correctionSpace
    exact (oldResolvent M
      ((oldInsertion hU hvol ν σ hν hσ k H
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P)).down)).property
  have hmemScalar : S.down ∈
      (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace := by
    simpa [M, scalarFrameRealization, hU, hvol,
      volume_openCubeSet_toReal] using hmem
  have hvariation := Native.old_signed_hilbert_correction_variation Q ν σ hν hσ k
    S.down hmemScalar
  simpa [S] using hvariation.2.1

/-- The flat first response `(0,-w_H)`, written as the actual pure-second
injection in the same fixed response-energy carrier. -/
noncomputable def flatFirstResponse {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (w : HilbertVectorL2 U) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  responseEnergyUp (responseFrameEnergyData hU hvol ν σ hν hσ k)
    (Variational.hilbertPureSecondL2 U (-w))

/-- Modewise `-w_H=P_D(H e_i)` from the actual main flat minus field.
The coordinate vector is formed from the certified zero-trace H¹ potentials,
not from a surrogate whole-space projection. -/
noncomputable def flatPureFluxMode (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) (i : Fin 2) :
    HilbertVectorL2 (openCubeSet Q) :=
  toHilbertVectorL2OfVecField
    (Native.old_signed_flat_minus_memL2 Q b L n i)

/-- The main flat minus mode is the actual local Dirichlet projection of the
whole-plane rotated source mode. -/
theorem flat_pure_flux_mode_eq_local_dirichlet_projection
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : Gaussian.whiteBasisIndex) (i : Fin 2) :
    flatPureFluxMode Q b L n i =
      lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
        (toHilbertVectorL2OfVecField
          (Native.old_signed_rotated_projected_memL2 Q b L
            (Gaussian.whiteBasis n) i)) := by
  exact Native.old_signed_flat_minus_is_dirichlet_projection Q b L n i

/-- The modewise flat response uses the source's actual DIAG/local Dirichlet
projection potential. `flatPureFluxMode` is the projected value `-w_H`,
so it is negated here before the defining `u₁_flat=(0,-w_H)` injection. -/
noncomputable def flatFirstResponseMode {Q : TriadicCube 2} (hU : MeasurableSet (openCubeSet Q))
    (hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) (i : Fin 2) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  flatFirstResponse hU hvol ν σ hν hσ k (-flatPureFluxMode Q b L n i)

/-- The exact OLD-minus-flat first-response defect. -/
noncomputable def firstResponseDefect {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) (H : ResponseCoefficient U)
    (w : HilbertVectorL2 U) : EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  oldFirstResponse hU hvol ν σ hν hσ k P H -
    flatFirstResponse hU hvol ν σ hν hσ k w

/-- Subtracting the actual flat pure-second response does not change the
first-potential carrier: the OLD-minus-flat defect still has a global H10
first potential, in the a.e. form used by the compatible source window. -/
theorem first_response_defect_first_potential_ae (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (H : ResponseCoefficient (openCubeSet Q)) (w : HilbertVectorL2 (openCubeSet Q)) :
    ∃ v : H10Function (openCubeSet Q),
      (fun x => (hilbertBlockL2ToBlockL2
        (firstResponseDefect (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k P H w).down x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        v.toH1Function.grad := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let first := oldFirstResponse (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    ν σ hν hσ k P H
  let flat := Variational.hilbertPureSecondL2 (openCubeSet Q) (-w)
  let defect := firstResponseDefect hU hvol ν σ hν hσ k P H w
  have hdown : defect.down = first.down - flat := by
    change first.down - (responseEnergyUp D flat).down = first.down - flat
    simp
  have hraw : hilbertBlockL2ToBlockL2 defect.down =
      hilbertBlockL2ToBlockL2 first.down - hilbertBlockL2ToBlockL2 flat := by
    rw [hdown]
    simp only [map_sub]
  have hflat : (fun x => (hilbertBlockL2ToBlockL2 flat x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] fun _ => (0 : Vec 2) := by
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (F := flat),
      ContinuousLinearMap.coeFn_compLpL (p := 2)
        (μ := volumeMeasureOn (openCubeSet Q))
        (L := Variational.hilbertPureSecond.toContinuousLinearMap) (f := -w)]
        with x htransport hcomp
    rw [htransport]
    have hcomp' : flat x =
        Variational.hilbertPureSecond.toContinuousLinearMap ((-w) x) := by
      simpa [flat, Variational.hilbertPureSecondL2] using hcomp
    rw [hcomp']
    change (Variational.hilbertPureSecond ((-w) x)).toBlockVec.1 = 0
    rw [Variational.hilbertPureSecond_toBlockVec]
  have hfirst : (fun x => (hilbertBlockL2ToBlockL2 defect.down x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => (hilbertBlockL2ToBlockL2 first.down x).1 := by
    filter_upwards [hflat, MeasureTheory.Lp.coeFn_sub
      (hilbertBlockL2ToBlockL2 first.down) (hilbertBlockL2ToBlockL2 flat)]
        with x hx hsub
    have hpoint := congrArg (fun z : BlockL2 (openCubeSet Q) => z x) hraw
    calc
      (hilbertBlockL2ToBlockL2 defect.down x).1 =
          ((hilbertBlockL2ToBlockL2 first.down -
            hilbertBlockL2ToBlockL2 flat) x).1 := congrArg Prod.fst hpoint
      _ = (hilbertBlockL2ToBlockL2 first.down x -
          hilbertBlockL2ToBlockL2 flat x).1 := congrArg Prod.fst hsub
      _ = (hilbertBlockL2ToBlockL2 first.down x).1 := by
        rw [Prod.fst_sub, hx, sub_zero]
  obtain ⟨v, hv⟩ := old_first_response_zero_trace_potential Q ν σ hν hσ k P H
  refine ⟨v, ?_⟩
  filter_upwards [hfirst] with x hx
  exact hx.trans (congrFun hv x).symm

/-- The physical second defect source `s_def=C_H δu₁`, before its exact
projected-source representative is supplied by the source-window identity. -/
noncomputable def secondDefectSource {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) (H : ResponseCoefficient U)
    (w : HilbertVectorL2 U) : EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  oldInsertion hU hvol ν σ hν hσ k H
    (firstResponseDefect hU hvol ν σ hν hσ k P H w)

/-- The two-index physical Wick operator: the `Hleft` shear acts on the
`Hright` OLD-minus-flat response defect. -/
noncomputable def secondDefectSourceBilinear {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2)
    (Hleft Hright : ResponseCoefficient U) (w : HilbertVectorL2 U) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  oldInsertion hU hvol ν σ hν hσ k Hleft
    (firstResponseDefect hU hvol ν σ hν hσ k P Hright w)

/-- The physical second defect shear has the exact compatible DIAG source
window: after projecting to the response-energy complement, it is the
projected-source load of the Lemma-V row field of the defect's genuine H10
first potential. -/
theorem second_defect_source_projection_eq (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (Hleft Hright : ResponseCoefficient (openCubeSet Q))
    (w : HilbertVectorL2 (openCubeSet Q)) (r : H10Function (openCubeSet Q))
    (η : PlanarW2Infinity Q)
    (hlink : η.value.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => responseCoefficientExtension Hleft x / σ)
    (hfirst : (fun x => (hilbertBlockL2ToBlockL2
      (firstResponseDefect (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν σ hν hσ k P Hright w).down x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        r.toH1Function.grad) :
    let hU := measurableSet_openCubeSet Q
    let hvol := by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
    let D := responseFrameEnergyData hU hvol ν σ hν hσ k
    let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
    let I := diagInterpolant Q 0
    let v := r.toH1Function
    let F := planarShearSourceField I η v
    let hF : MemLp F 2 (normalizedCubeMeasure Q) := by
      have hη : MemLp η.value.toFun ⊤ (volume.restrict (openCubeSet Q)) :=
        η.value_memLp_top
      have hDη : ∀ i, MemLp (fun x => η.value.grad x i) ⊤
          (volume.restrict (openCubeSet Q)) :=
        fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
      have hrow := lemmaVPlanarRowField_memL2 I η.value v hη hDη
      have hrowEq : F = fun x => -lemmaVPlanarRowField I η.value v x := by
        funext x i
        rw [lemmaVH2_rowField_eq]
        simp [F, planarShearSourceField, planarQuarterTurn]
      have hFvec : MemVectorL2 (openCubeSet Q) F := by
        rw [hrowEq]
        exact hrow.neg
      apply MemLp.of_eval
      intro i
      exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 hFvec i)
    V.toSubmoduleᗮ.starProjection
      (secondDefectSourceBilinear hU hvol ν σ hν hσ k P Hleft Hright w) =
      V.toSubmoduleᗮ.starProjection
        (responseEnergyUp D (projectedSourceLoad Q hF)) := by
  classical
  dsimp only
  let U := openCubeSet Q
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let I := diagInterpolant Q 0
  let v := r.toH1Function
  let F := planarShearSourceField I η v
  have hφ : lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) 0 r = v := by
    ext x
    · simp only [lemmaVAffinePotential, H1Function.add_toFun,
        H1Function.affineOnIsSobolevRegularDomain_apply]
      simp [v]
    · simp only [lemmaVAffinePotential, H1Function.add_grad,
        H1Function.affineOnIsSobolevRegularDomain_grad]
      simp [v]
  have hres : MemH10 U (v-I v).toFun := by
    simpa [I, v, hφ] using
      diagInterpolant_affine_residual_memH10 Q 0 0 r
  have hη : MemLp η.value.toFun ⊤ (volume.restrict U) := η.value_memLp_top
  have hDη : ∀ i, MemLp (fun x => η.value.grad x i) ⊤ (volume.restrict U) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  have hrow := lemmaVPlanarRowField_memL2 I η.value v hη hDη
  have hrowEq : F = fun x => -lemmaVPlanarRowField I η.value v x := by
    funext x i
    rw [lemmaVH2_rowField_eq]
    simp [F, planarShearSourceField, planarQuarterTurn]
  have hFvec : MemVectorL2 U F := by
    rw [hrowEq]
    exact hrow.neg
  have hF : MemLp F 2 (normalizedCubeMeasure Q) := by
    apply MemLp.of_eval
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hsource : F = planarShearSourceField I η v := rfl
  have hbridge := planar_response_shear_complement_eq
    Q hU hvol ν σ hν hσ k Hleft
    (firstResponseDefect hU hvol ν σ hν hσ k P Hright w)
    I η v hres F hF hsource hlink hfirst
  change V.toSubmoduleᗮ.starProjection
      (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k Hleft
        (firstResponseDefect hU hvol ν σ hν hσ k P Hright w)) =
    V.toSubmoduleᗮ.starProjection
      (responseEnergyUp D (projectedSourceLoad Q hF))
  exact hbridge

/-- The source-indexed first-response defect mode, for the unit pure-flux
load `e_i`. The flat component is the actual main Dirichlet projection
of that same q3 white mode. -/
noncomputable def q3DefectResponseMode (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (i : Fin 2) (n : whiteBasisIndex) :
    EnergyCarrier (responseFrameEnergyData (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k) :=
  firstResponseDefect (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    ν σ hν hσ k (basisVec i, 0)
    (σ • mainShellResponseCoefficient Q b L (whiteBasis n))
    (-flatPureFluxMode Q b L n i)

/-- The source's broken weak-Haar energy of one actual OLD-minus-flat response
mode. -/
noncomputable def q3DefectWeakModeEnergy (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) : ℝ :=
  Native.oldSignedBlockWeakNorm Q (fun x =>
    (hilbertBlockL2ToBlockL2
      (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x)) ^ 2

/-- The modal Gaussian-Hilbert budget of the physical first-response defect,
with the actual four-component broken weak-Haar norm on each load. -/
noncomputable def q3DefectLambda (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) : ℝ :=
  ∑ load : Fin 2, ∑' n : whiteBasisIndex,
    q3DefectWeakModeEnergy Q ν σ hν hσ k b L load n

/-- Each physical q3 response defect mode has its genuine zero-trace H10
first potential; the flat subtraction is retained in the second block. -/
theorem q3_defect_response_mode_first_potential (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) :
    ∃ r : H10Function (openCubeSet Q),
      (fun x => (hilbertBlockL2ToBlockL2
        (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x).1) =ᵐ[
          volumeMeasureOn (openCubeSet Q)] r.toH1Function.grad := by
  exact first_response_defect_first_potential_ae Q ν σ hν hσ k
    (basisVec load, 0)
    (σ • mainShellResponseCoefficient Q b L (whiteBasis n))
    (-flatPureFluxMode Q b L n load)

/-- The first-potential weak-Haar energy of a mode is dominated by its full
four-component broken weak-Haar energy. -/
theorem q3_defect_first_weak_energy_le_mode_energy (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) :
    vectorWeakHaarEnergy Q (fun x => (hilbertBlockL2ToBlockL2
      (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x).1) ≤
      q3DefectWeakModeEnergy Q ν σ hν hσ k b L load n := by
  let F : Vec 2 → BlockVec 2 := fun x =>
    hilbertBlockL2ToBlockL2
      (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x
  rw [q3DefectWeakModeEnergy]
  unfold Native.oldSignedBlockWeakNorm
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  change vectorWeakHaarEnergy Q (fun x => (F x).1) ≤
    vectorWeakHaarNorm Q (fun x => (F x).1) ^ 2 +
      vectorWeakHaarNorm Q (fun x => (F x).2) ^ 2
  rw [show vectorWeakHaarNorm Q (fun x => (F x).1) ^ 2 =
        vectorWeakHaarEnergy Q (fun x => (F x).1) by
        unfold vectorWeakHaarNorm
        exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q (fun x => (F x).1)),
      show vectorWeakHaarNorm Q (fun x => (F x).2) ^ 2 =
        vectorWeakHaarEnergy Q (fun x => (F x).2) by
        unfold vectorWeakHaarNorm
        exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q (fun x => (F x).2))]
  exact le_add_of_nonneg_right (vectorWeakHaarEnergy_nonneg Q (fun x => (F x).2))

/-- The two-index source coefficient `C_{H_i} δu₁(H_j)` on the physical
q3 mode family. -/
noncomputable def q3DefectShearMode (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2)
    (i j : whiteBasisIndex) :
    EnergyCarrier (responseFrameEnergyData (measurableSet_openCubeSet Q)
      (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ k) :=
  secondDefectSourceBilinear (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
    ν σ hν hσ k (basisVec load, 0)
    (σ • mainShellResponseCoefficient Q b L (whiteBasis i))
    (σ • mainShellResponseCoefficient Q b L (whiteBasis j))
    (-flatPureFluxMode Q b L j load)

end

end ASDExplicitGamma.Scalar
