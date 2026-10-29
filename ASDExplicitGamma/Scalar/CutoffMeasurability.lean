module

public import ASDExplicitGamma.Scalar.OldCutoffCoefficient
public import ASDExplicitGamma.Scalar.CutoffProjection
public import ASDExplicitGamma.Scalar.ProjectionRealization
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.ContinuousMap.Compact

/-! Measurability of the literal coefficient on compact cell closures. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization Response MeasureTheory Algsuperdiff.Section3
open scoped RealInnerProductSpace

noncomputable instance hilbertBlockL2_measurableSpace {U : Set (Vec 2)} :
    MeasurableSpace (HilbertBlockL2 U) := borel _

instance hilbertBlockL2_borelSpace {U : Set (Vec 2)} :
    BorelSpace (HilbertBlockL2 U) := ⟨rfl⟩

private theorem bilin_polarization {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (x y : V) :
    4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) := by
  have hp : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [B.map_add₂]
    rw [(B x).map_add, (B y).map_add]
    ring
  have hm : B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
    rw [B.map_sub₂]
    rw [(B x).map_sub, (B y).map_sub]
    ring
  rw [hp, hm, hB y x]
  ring

/-- Pull back a symmetric energy form by a bounded linear change of variables. -/
private noncomputable def pullbackBilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : V →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR V B).flip T).comp T

/-- Restriction in both arguments is continuous linear in the ambient form. -/
private noncomputable def restrictBilinCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) := by
  let i : K.toSubmodule →L[ℝ] V := K.toSubmodule.subtypeL
  let hOuter : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] V →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V (V →L[ℝ] ℝ)).flip i
  let hInner : (V →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V ℝ).flip i
  exact (ContinuousLinearMap.compL ℝ K.toSubmodule
    (V →L[ℝ] ℝ) (K.toSubmodule →L[ℝ] ℝ) hInner).comp hOuter

private theorem restrictBilinCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    restrictBilinCLM K B = Homogenization.restrictBilin K B := by
  ext x y
  rfl

/-- The Riesz representation of a restricted form depends continuously on
the ambient form. -/
private noncomputable def restrictedBilinOperatorCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) :
    (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
  ContinuousLinearMap.compL ℝ K.toSubmodule (K.toSubmodule →L[ℝ] ℝ)
    K.toSubmodule
    (((InnerProductSpace.toDual ℝ K.toSubmodule).symm).toContinuousLinearEquiv
      |>.toContinuousLinearMap)

private theorem restrictedBilinOperatorCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    restrictedBilinOperatorCLM K (restrictBilinCLM K B) =
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K B) := by
  simp [restrictedBilinOperatorCLM, InnerProductSpace.continuousLinearMapOfBilin,
    restrictBilinCLM_apply]

/-- The affine right-hand side depends continuously on the ambient form. -/
private noncomputable def subspaceRhsCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (x : V) :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] K.toSubmodule := by
  let i : K.toSubmodule →L[ℝ] V := K.toSubmodule.subtypeL
  let eval : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) x
  let restrict : (V →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V ℝ).flip i
  let neg : (K.toSubmodule →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) := -1
  exact (Homogenization.subspaceRieszMap K).comp (neg.comp (restrict.comp eval))

private theorem subspaceRhsCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (x : V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    subspaceRhsCLM K x B = Homogenization.subspaceRhs K B x := by
  apply congrArg (Homogenization.subspaceRieszMap K)
  ext y
  simp [subspaceRhsCLM, Homogenization.subspaceRhsBilin_apply]

/-- The coefficient-dependent frame form is a pullback of the zero-skew
frame form by the physical shear. -/
private theorem scalarFrame_energyBilin_eq_pullback
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin =
      pullbackBilin
        (scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient (openCubeSet Q))).energyBilin
        (1 + responseShearL2Operator σ hσ k) := by
  letI finiteEnergyVolume : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let U := openCubeSet Q
  let Bk := (scalarFrameRealization Q ν σ hν hσ k).energyBilin
  let B0 := (scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient U)).energyBilin
  let T := (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
    responseShearL2Operator σ hσ k
  have hBk : ∀ x y, Bk x y = Bk y x := by
    exact (scalarFrameRealization Q ν σ hν hσ k).energySymm
  have hB0 : ∀ x y, B0 x y = B0 y x := by
    exact (scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient U)).energySymm
  have hdiag (x : HilbertBlockL2 U) : Bk x x = B0 (T x) (T x) := by
    let hvol : 0 < (MeasureTheory.volume U).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos Q
    change (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
      hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin x x =
      (responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
        hvol ν σ hν hσ (0 : ResponseCoefficient U)).toMuHilbertRealization.energyBilin
        (T x) (T x)
    have hshear := responseFrameMu_energy_shear_identity
      (measurableSet_openCubeSet Q) hvol ν σ hν hσ
      (0 : ResponseCoefficient U) k x
    rw [zero_add] at hshear
    have hT : T x = x + responseShearL2Operator σ hσ k x := by
      simp [T]
    simpa only [hT] using hshear.symm
  have hpair (x y : HilbertBlockL2 U) : Bk x y = B0 (T x) (T y) := by
    have hleft := bilin_polarization Bk hBk x y
    have hright := bilin_polarization B0 hB0 (T x) (T y)
    have hadd : T (x + y) = T x + T y := T.map_add x y
    have hsub : T (x - y) = T x - T y := T.map_sub x y
    rw [hdiag (x + y), hdiag (x - y)] at hleft
    rw [hadd, hsub] at hleft
    calc
      Bk x y = (4 * Bk x y) / 4 := by ring
      _ = (4 * B0 (T x) (T y)) / 4 := by rw [hleft, ← hright]
      _ = B0 (T x) (T y) := by ring
  ext x y
  change Bk x y = B0 (T x) (T y)
  exact hpair x y

/-- Use the Borel sigma algebra on the bounded-continuous coefficient space
of a fixed cell. -/
noncomputable instance responseCoefficient_measurableSpace (Q : TriadicCube 2) :
    MeasurableSpace (ResponseCoefficient (openCubeSet Q)) := borel _

/-- The preceding coefficient sigma algebra is its canonical Borel one. -/
noncomputable instance responseCoefficient_borelSpace (Q : TriadicCube 2) :
    BorelSpace (ResponseCoefficient (openCubeSet Q)) := ⟨rfl⟩

/-- The actual old cutoff skew coefficient is measurable as a bounded
continuous coefficient on the closed cell. -/
theorem measurable_oldCutoffSkewCoefficient (n : ℤ) (Q : TriadicCube 2) :
    Measurable fun ω : Cutoff.CutoffSample 2 => oldCutoffSkewCoefficient n Q ω := by
  letI compactOldCutoffSquare : CompactSpace (closure (openCubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
  let f : Cutoff.CutoffSample 2 → C(closure (openCubeSet Q), ℝ) := fun ω =>
    ⟨fun x => Cutoff.cutoff n ω x.1 1 0,
      (Cutoff.continuous_cutoffValue_entry n ω 1 0).comp continuous_subtype_val⟩
  have hf : Measurable f := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro x
    exact Cutoff.measurable_cutoff_apply_entry n x.1 1 0
  have hmk : Measurable fun ω => BoundedContinuousFunction.mkOfCompact (f ω) :=
    (ContinuousMap.isometryEquivBoundedOfCompact
      (closure (openCubeSet Q)) ℝ).continuous.measurable.comp hf
  simpa [f, oldCutoffSkewCoefficient] using hmk

private theorem continuous_pullbackBilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous fun T : V →L[ℝ] V => pullbackBilin B T := by
  fun_prop [pullbackBilin]

/-- The sample-dependent cell energy form is a measurable family of bounded
bilinear forms. -/
theorem measurable_oldCutoff_scalarFrameEnergyBilin
    (n : ℤ) (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) :
    Measurable fun ω : Cutoff.CutoffSample 2 =>
      (scalarFrameRealization Q ν σ hν hσ (oldCutoffSkewCoefficient n Q ω)).energyBilin := by
  let U := openCubeSet Q
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient U)).energyBilin
  let F : ResponseCoefficient U →
      (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) :=
    fun k => pullbackBilin B0
      (1 + responseShearL2Operator σ hσ k)
  have hS : Continuous fun k : ResponseCoefficient U =>
      responseShearL2Operator σ hσ k :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  have hF : Continuous fun k : ResponseCoefficient U => F k := by
    have hT : Continuous fun k : ResponseCoefficient U =>
        (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
          responseShearL2Operator σ hσ k := continuous_const.add hS
    exact (continuous_pullbackBilin B0).comp hT
  have hk : Measurable fun ω : Cutoff.CutoffSample 2 =>
      oldCutoffSkewCoefficient n Q ω := measurable_oldCutoffSkewCoefficient n Q
  have hmeas : Measurable fun ω : Cutoff.CutoffSample 2 =>
      F (oldCutoffSkewCoefficient n Q ω) := hF.measurable.comp hk
  have hEq : (fun ω : Cutoff.CutoffSample 2 =>
      (scalarFrameRealization Q ν σ hν hσ (oldCutoffSkewCoefficient n Q ω)).energyBilin) =
        fun ω => F (oldCutoffSkewCoefficient n Q ω) := by
    funext ω
    exact scalarFrame_energyBilin_eq_pullback Q ν σ hν hσ
      (oldCutoffSkewCoefficient n Q ω)
  rw [hEq]
  exact hmeas

private theorem scalarFrame_correctionSpace_eq_zero (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace =
      (scalarFrameRealization Q ν σ hν hσ
        (0 : ResponseCoefficient (openCubeSet Q))).correctionSpace.correctionSpace := by
  let U := openCubeSet Q
  let M₁ := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  let M₀ := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ
      (0 : ResponseCoefficient U)
  have hsys : M₁.correctionSpace = M₀.correctionSpace := by
    change (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData =
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData
    rfl
  change M₁.correctionSpace.correctionSpace = M₀.correctionSpace.correctionSpace
  rw [hsys]

/-- The actual affine cell minimizer depends measurably on the cutoff sample.
The correction space is coefficient-independent, while the complete energy
form varies continuously through the physical shear. -/
theorem measurable_oldCutoff_scalarProjectionResidual
    (n : ℤ) (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (F : HilbertBlockL2 (openCubeSet Q)) :
    Measurable fun ω : Cutoff.CutoffSample 2 =>
      scalarProjectionResidual Q ν σ hν hσ (oldCutoffSkewCoefficient n Q ω) F := by
  let U := openCubeSet Q
  letI finiteEnergyVolume : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let M₀ := scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient U)
  let K := M₀.correctionSpace.correctionSpace
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient U :=
    oldCutoffSkewCoefficient n Q
  let B : Cutoff.CutoffSample 2 → HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ :=
    fun ω => (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin
  let hCoercive : ∀ ω, IsCoercive (B ω) := fun ω =>
    (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyCoercive
  letI : IsSeparable (volumeMeasureOn U) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 U) := inferInstance
  letI : BorelSpace K.toSubmodule := inferInstance
  letI : SecondCountableTopology K.toSubmodule := inferInstance
  have hProduct : OpensMeasurableSpace
      ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule) := inferInstance
  have hB : Measurable B := by
    exact measurable_oldCutoff_scalarFrameEnergyBilin n Q ν σ hν hσ
  let sharpMap : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
    (restrictedBilinOperatorCLM K).comp (restrictBilinCLM K)
  have hSharp : Measurable fun ω =>
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K (B ω)) := by
    have hm : Measurable fun ω => sharpMap (B ω) :=
      sharpMap.continuous.measurable.comp hB
    have heq : (fun ω => sharpMap (B ω)) = fun ω =>
        InnerProductSpace.continuousLinearMapOfBilin
          (Homogenization.restrictBilin K (B ω)) := by
      funext ω
      exact restrictedBilinOperatorCLM_apply K (B ω)
    rw [← heq]
    exact hm
  let rhsMap : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) →L[ℝ]
      K.toSubmodule := subspaceRhsCLM K F
  have hRhs : Measurable fun ω => Homogenization.subspaceRhs K (B ω) F := by
    have hm : Measurable fun ω => rhsMap (B ω) :=
      rhsMap.continuous.measurable.comp hB
    have heq : (fun ω => rhsMap (B ω)) = fun ω =>
        Homogenization.subspaceRhs K (B ω) F := by
      funext ω
      exact subspaceRhsCLM_apply K F (B ω)
    rw [← heq]
    exact hm
  have hMin : Measurable fun ω =>
      Homogenization.affineMinimizerMap K (B ω) (hCoercive ω) F := by
    exact Measurable.affineMinimizerMap_apply (K := K) (hB := hCoercive)
      (x := fun _ => F) measurable_const hSharp hRhs
  have hEq : (fun ω => scalarProjectionResidual Q ν σ hν hσ (coeff ω) F) =
      fun ω => Homogenization.affineMinimizerMap K (B ω) (hCoercive ω) F := by
    funext ω
    rw [scalarProjectionResidual_eq_affineMinimizer]
    rw [scalarFrame_correctionSpace_eq_zero Q ν σ hν hσ (coeff ω)]
  rw [hEq]
  exact hMin

end ASDExplicitGamma.Scalar
