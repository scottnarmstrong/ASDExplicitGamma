module

public import ASDExplicitGamma.Main.EOscillation
public import ASDExplicitGamma.Main.MultiplierMoments
public import ASDExplicitGamma.Statements.GammaZero
public import ASDExplicitGamma.Statements.Theta
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Gaussian.RioTwoSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Gaussian.SquareMinimizer
public import ASDExplicitGamma.Native.OldSignedAffineCorrectorBounds
public import ASDExplicitGamma.Main.Q3MultiplierScale
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Main.Q3RowCaps
public import ASDExplicitGamma.Main.Q3ColumnProduct
public import ASDExplicitGamma.Main.ColumnProductCaps
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import Homogenization.Sobolev.Foundations.H10Graph
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! The actual cutoff-sample affine minimizer carrier for the oscillation row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Variational Algsuperdiff.Section3
open ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff
open scoped RealInnerProductSpace

noncomputable section

local instance mainEoscFiniteEnergyVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

local instance mainEoscVolumeSeparable (Q : TriadicCube 2) :
    IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance

local instance mainEoscFactTwoLe : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

local instance mainEoscFactTwoNeTop : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

local instance mainEoscHilbertBlockSecondCountable (Q : TriadicCube 2) :
    SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance

local instance mainEoscCorrectionBorel (Q : TriadicCube 2)
    (K : ClosedSubmodule ℝ (HilbertBlockL2 (openCubeSet Q))) :
    BorelSpace K.toSubmodule := inferInstance

local instance mainEoscCorrectionSecondCountable (Q : TriadicCube 2)
    (K : ClosedSubmodule ℝ (HilbertBlockL2 (openCubeSet Q))) :
    SecondCountableTopology K.toSubmodule := inferInstance

local instance mainEoscCompactSquare (Q : TriadicCube 2) :
    CompactSpace (closure (openCubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure

private theorem eosc_bilin_polarization {V : Type*}
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

private noncomputable def eosc_pullbackBilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : V →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR V B).flip T).comp T

private theorem eosc_scalarFrame_energyBilin_eq_pullback
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin =
      eosc_pullbackBilin
        (scalarFrameRealization Q ν σ hν hσ
          (0 : ResponseCoefficient (openCubeSet Q))).energyBilin
        (1 + responseShearL2Operator σ hσ k) := by
  let U := openCubeSet Q
  let Bk := (scalarFrameRealization Q ν σ hν hσ k).energyBilin
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient U)).energyBilin
  let T := (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
    responseShearL2Operator σ hσ k
  have hBk : ∀ x y, Bk x y = Bk y x := fun x y =>
    (scalarFrameRealization Q ν σ hν hσ k).energySymm x y
  have hB0 : ∀ x y, B0 x y = B0 y x := fun x y =>
    (scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient U)).energySymm x y
  have hdiag (x : HilbertBlockL2 U) : Bk x x = B0 (T x) (T x) := by
    let hvol : 0 < (volume U).toReal := by
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
    have hleft := eosc_bilin_polarization Bk hBk x y
    have hright := eosc_bilin_polarization B0 hB0 (T x) (T y)
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

private theorem eosc_scalarFrame_correctionSpace_eq_zero (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace =
      (scalarFrameRealization Q ν σ hν hσ
        (0 : ResponseCoefficient (openCubeSet Q))).correctionSpace.correctionSpace := by
  let U := openCubeSet Q
  let M₁ := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q) ν σ hν hσ k
  let M₀ := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q)
    (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
      ν σ hν hσ (0 : ResponseCoefficient U)
  have hsys : M₁.correctionSpace = M₀.correctionSpace := by
    change (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData =
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData
    rfl
  change M₁.correctionSpace.correctionSpace = M₀.correctionSpace.correctionSpace
  rw [hsys]

private noncomputable def eosc_restrictBilinCLM {V : Type*}
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

private theorem eosc_restrictBilinCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    eosc_restrictBilinCLM K B = Homogenization.restrictBilin K B := by
  ext x y
  rfl

private noncomputable def eosc_restrictedBilinOperatorCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) :
    (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
  ContinuousLinearMap.compL ℝ K.toSubmodule (K.toSubmodule →L[ℝ] ℝ)
    K.toSubmodule
    (((InnerProductSpace.toDual ℝ K.toSubmodule).symm).toContinuousLinearEquiv
      |>.toContinuousLinearMap)

private theorem eosc_restrictedBilinOperatorCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    eosc_restrictedBilinOperatorCLM K (eosc_restrictBilinCLM K B) =
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K B) := by
  simp [eosc_restrictedBilinOperatorCLM, InnerProductSpace.continuousLinearMapOfBilin,
    eosc_restrictBilinCLM_apply]

private noncomputable def eosc_subspaceRhsCLM {V : Type*}
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

private theorem eosc_subspaceRhsCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (x : V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    eosc_subspaceRhsCLM K x B = Homogenization.subspaceRhs K B x := by
  apply congrArg (Homogenization.subspaceRieszMap K)
  ext y
  simp [Homogenization.subspaceRhsBilin_apply]

private theorem continuous_eosc_pullbackBilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous fun T : V →L[ℝ] V => eosc_pullbackBilin B T := by
  fun_prop [eosc_pullbackBilin]

private theorem eosc_measurable_affineMinimizerMap_apply
    {Ω V : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [MeasurableAdd₂ V]
    (K : ClosedSubmodule ℝ V) [BorelSpace K.toSubmodule]
    [OpensMeasurableSpace
      ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule)]
    {B : Ω → V →L[ℝ] V →L[ℝ] ℝ} {hB : ∀ ω, IsCoercive (B ω)}
    {x : Ω → V} (hx : Measurable x)
    (hSharp : Measurable fun ω =>
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K (B ω)))
    (hRhs : Measurable fun ω => Homogenization.subspaceRhs K (B ω) (x ω)) :
    Measurable fun ω => Homogenization.affineMinimizerMap K (B ω) (hB ω) (x ω) :=
  Measurable.affineMinimizerMap_apply K hx hSharp hRhs

private theorem measurable_eosc_scalarFrameEnergyBilin_of_measurable_coefficient
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (coeff : Cutoff.CutoffSample 2 → ResponseCoefficient (openCubeSet Q))
    (hcoeff : Measurable coeff) :
    Measurable fun ω : Cutoff.CutoffSample 2 =>
      (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin := by
  let U := openCubeSet Q
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient U)).energyBilin
  let Fk : ResponseCoefficient U →
      HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ := fun k =>
    eosc_pullbackBilin B0 (1 + responseShearL2Operator σ hσ k)
  have hS : Continuous fun k : ResponseCoefficient U =>
      responseShearL2Operator σ hσ k :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  have hFk : Continuous Fk := by
    have hT : Continuous fun k : ResponseCoefficient U =>
        (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
          responseShearL2Operator σ hσ k := continuous_const.add hS
    exact (continuous_eosc_pullbackBilin B0).comp hT
  have hEq : (fun ω : Cutoff.CutoffSample 2 =>
      (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin) =
      fun ω => Fk (coeff ω) := by
    funext ω
    exact eosc_scalarFrame_energyBilin_eq_pullback Q ν σ hν hσ (coeff ω)
  rw [hEq]
  exact hFk.measurable.comp hcoeff

theorem measurable_scalarProjectionResidual_of_measurable_coefficient
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (coeff : Cutoff.CutoffSample 2 → ResponseCoefficient (openCubeSet Q))
    (hcoeff : Measurable coeff) (F : HilbertBlockL2 (openCubeSet Q)) :
    Measurable fun ω : Cutoff.CutoffSample 2 =>
      scalarProjectionResidual Q ν σ hν hσ (coeff ω) F := by
  let U := openCubeSet Q
  let M₀ := scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient U)
  let K := M₀.correctionSpace.correctionSpace
  let B : Cutoff.CutoffSample 2 → HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ :=
    fun ω => (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin
  let hCoercive : ∀ ω, IsCoercive (B ω) := fun ω =>
    (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyCoercive
  have hProduct : OpensMeasurableSpace
      ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule) := inferInstance
  have hB : Measurable B := by
    exact measurable_eosc_scalarFrameEnergyBilin_of_measurable_coefficient
      Q ν σ hν hσ coeff hcoeff
  let sharpMap : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
    (eosc_restrictedBilinOperatorCLM K).comp (eosc_restrictBilinCLM K)
  have hSharp : Measurable fun ω =>
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K (B ω)) := by
    have hm : Measurable fun ω => sharpMap (B ω) :=
      sharpMap.continuous.measurable.comp hB
    have heq : (fun ω => sharpMap (B ω)) = fun ω =>
        InnerProductSpace.continuousLinearMapOfBilin
          (Homogenization.restrictBilin K (B ω)) := by
      funext ω
      exact eosc_restrictedBilinOperatorCLM_apply K (B ω)
    rw [← heq]
    exact hm
  let rhsMap : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) →L[ℝ]
      K.toSubmodule := eosc_subspaceRhsCLM K F
  have hRhs : Measurable fun ω => Homogenization.subspaceRhs K (B ω) F := by
    have hm : Measurable fun ω => rhsMap (B ω) :=
      rhsMap.continuous.measurable.comp hB
    have heq : (fun ω => rhsMap (B ω)) = fun ω =>
        Homogenization.subspaceRhs K (B ω) F := by
      funext ω
      exact eosc_subspaceRhsCLM_apply K F (B ω)
    rw [← heq]
    exact hm
  have hMin : Measurable fun ω =>
      Homogenization.affineMinimizerMap K (B ω) (hCoercive ω) F := by
    exact eosc_measurable_affineMinimizerMap_apply
      (Ω := Cutoff.CutoffSample 2) (V := HilbertBlockL2 U)
      (K := K) (B := B) (hB := hCoercive) (x := fun _ => F)
      measurable_const hSharp hRhs
  have hEq : (fun ω => scalarProjectionResidual Q ν σ hν hσ (coeff ω) F) =
      fun ω => Homogenization.affineMinimizerMap K (B ω) (hCoercive ω) F := by
    funext ω
    rw [scalarProjectionResidual_eq_affineMinimizer]
    rw [eosc_scalarFrame_correctionSpace_eq_zero Q ν σ hν hσ (coeff ω)]
  rw [hEq]
  exact hMin

/-- The OLD-frame skew coefficient at insertion time `t`, restricted to the
closed observation square.  Its symmetric part is absent by construction. -/
noncomputable def mainInsertionSkewCoefficient
    (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ResponseCoefficient (openCubeSet Q) := by
  refine BoundedContinuousFunction.mkOfCompact
    ⟨fun x => Cutoff.cutoff m ω x.1 1 0 +
        Real.sqrt t * (ω.1 (m + 1) x.1 1 0), ?_⟩
  exact ((Cutoff.continuous_cutoffValue_entry m ω 1 0).add
    (continuous_const.mul (by fun_prop :
      Continuous (fun x : Vec 2 => ω.1 (m + 1) x 1 0)))).comp continuous_subtype_val

/-- The OLD-frame partial-insertion skew coefficient is measurable as a
bounded continuous coefficient on the closed local square. -/
theorem measurable_mainInsertionSkewCoefficient
    (m : ℤ) (t : ℝ) (Q : TriadicCube 2) :
    Measurable fun ω : Cutoff.CutoffSample 2 =>
      mainInsertionSkewCoefficient m t Q ω := by
  let f : Cutoff.CutoffSample 2 → C(closure (openCubeSet Q), ℝ) := fun ω =>
    ⟨fun x => Cutoff.cutoff m ω x.1 1 0 +
        Real.sqrt t * (ω.1 (m + 1) x.1 1 0), by
      exact ((Cutoff.continuous_cutoffValue_entry m ω 1 0).add
        (continuous_const.mul (by fun_prop :
          Continuous (fun x : Vec 2 => ω.1 (m + 1) x 1 0)))).comp continuous_subtype_val⟩
  have hf : Measurable f := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro x
    have hFresh : Measurable fun ω : Cutoff.CutoffSample 2 =>
        ω.1 (m + 1) x.1 1 0 := by
      exact (Algsuperdiff.Frozen.Assumptions.ShellField.measurable_eval_entry
        x.1 1 0).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
    exact (Cutoff.measurable_cutoff_apply_entry m x.1 1 0).add
      (measurable_const.mul hFresh)
  have hmk : Measurable fun ω => BoundedContinuousFunction.mkOfCompact (f ω) :=
    (ContinuousMap.isometryEquivBoundedOfCompact
      (closure (openCubeSet Q)) ℝ).continuous.measurable.comp hf
  simpa [f, mainInsertionSkewCoefficient] using hmk

/-- The sample-indexed OLD-frame affine minimizer as an actual Hilbert-L²
field. The underlying weighted projection is measurable by the
coefficient-independent correction-space construction. -/
noncomputable def mainCutoffAffineMinimizer
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (m : ℤ) (t : ℝ) (P : BlockVec 2)
    (hP : MemBlockL2 (openCubeSet Q) (fun _ : Vec 2 => P)) :
    Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q) :=
  fun ω => scalarProjectionResidual Q ν σ hν hσ
    (mainInsertionSkewCoefficient m t Q ω)
    (toHilbertBlockL2OfBlockField hP)

/-- Measurability of the actual partial-insertion affine minimizer in the
standard Hilbert carrier. -/
theorem measurable_mainCutoffAffineMinimizer
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (m : ℤ) (t : ℝ) (P : BlockVec 2)
    (hP : MemBlockL2 (openCubeSet Q) (fun _ : Vec 2 => P)) :
    Measurable (mainCutoffAffineMinimizer Q ν σ hν hσ m t P hP) := by
  exact measurable_scalarProjectionResidual_of_measurable_coefficient
    Q ν σ hν hσ (mainInsertionSkewCoefficient m t Q)
    (measurable_mainInsertionSkewCoefficient m t Q)
    (toHilbertBlockL2OfBlockField hP)

end
end ASDExplicitGamma.Main
