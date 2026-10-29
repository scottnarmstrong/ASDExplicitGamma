module

public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualL128
public import ASDExplicitGamma.Scalar.PhysicalResolventParity

/-! The H10 source carrier and exact physical action relevant to the flat
NEW-resolvent bridge. This module records the Dirichlet-projected source
without identifying it with a second application of the physical shear. -/

@[expose] public section

open MeasureTheory Homogenization
open scoped ENNReal
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

namespace ASDExplicitGamma.Scalar

local instance flatResolventFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The q3 Dirichlet-projected source as an actual zero-trace H10 potential
gradient, on the same potential carrier as the physical resolvent. -/
noncomputable def flatSourcePotentialCarrier
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    (physicalPotentialSpace Q).toSubmodule := by
  let hDom := isOpenBoundedConvexDomain_openCubeSet Q
  refine ⟨lambda8Q3ProjectedLoadClass hDom a₀ b₀ c₀ d₀ hab hcd e z, ?_⟩
  change lambda8Q3ProjectedLoadClass hDom a₀ b₀ c₀ d₀ hab hcd e z ∈
    PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q)
  rw [PotentialSolenoidalExact.mem_potentialZeroTrace_iff]
  change ∃ u : H10Function (openCubeSet Q),
    u.toH1Function.gradToHilbertVectorL2 =
      lambda8DirichletProjection hDom
        (lambda8Q3LoadClass hDom.1.measurableSet a₀ b₀ c₀ d₀ hab hcd e z)
  exact lambda8DirichletProjection_isPotentialZeroTrace hDom
    (lambda8Q3LoadClass hDom.1.measurableSet a₀ b₀ c₀ d₀ hab hcd e z)

/-- Forgetting the subtype recovers exactly the source's fixed Dirichlet
projection. -/
theorem flat_source_potential_carrier_coe
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    (flatSourcePotentialCarrier Q hab hcd e z : HilbertVectorL2 (openCubeSet Q)) =
      lambda8Q3ProjectedLoadClass
        (isOpenBoundedConvexDomain_openCubeSet Q)
        a₀ b₀ c₀ d₀ hab hcd e z := rfl

/-- The fixed Wick representative is the shell scalar times this
Dirichlet-projected source carrier. -/
theorem flat_source_potential_carrier_wick_eq
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (k : ℤ) (ω : Cutoff.CutoffSample 2) :
    flatSourceQ3ActualWickRepresentative Q hab hcd e k ω =
      flatSourceQ3ShellValueLInf Q hab hcd
        (shellFieldScalarRestriction (closedRectangle a₀ b₀ c₀ d₀) (ω.1 k)) •
        (flatSourcePotentialCarrier Q hab hcd e
          (shellFieldScalarRestriction
            (closedRectangle a₀ b₀ c₀ d₀) (ω.1 k)) :
          HilbertVectorL2 (openCubeSet Q)) := rfl

/-- Before the outer flux projection, the physical positive-shear action has
the fixed plus sign `(H/σ) J p`. -/
theorem physical_positive_shear_to_plain_ae
    (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q))
    (p : HilbertVectorL2 (openCubeSet Q)) :
    hilbertVectorL2ToVectorL2
        (physicalPositiveShear Q σ hσ H p) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
  let U := openCubeSet Q
  let S := responseShearL2Operator σ hσ H (hilbertPureFirstL2 U p)
  have hinsert : hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p) =ᵐ[
      volumeMeasureOn U] fun x => (hilbertVectorL2ToVectorL2 p x, 0) := by
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p),
      ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
        (L := pureFirst.toContinuousLinearMap) (f := p),
      coeFn_hilbertVectorL2ToVectorL2 p] with x hblock hinsert hp
    rw [hblock]
    change ((pureFirst.toContinuousLinearMap.compLpL 2
      (volumeMeasureOn U) p) x).toBlockVec = _
    rw [hinsert, hp]
    apply Prod.ext
    · ext i
      simp [pureFirst, HilbertVec.toVec]
    · ext i
      simp [pureFirst, HilbertVec.toVec]
  have hproj : hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) =ᵐ[
      volumeMeasureOn U] fun x => (hilbertBlockL2ToBlockL2 S x).2 := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2)
        (μ := volumeMeasureOn U) (L := hilbertBlockSecondProjectionVec) (f := S),
      coeFn_hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S),
      coeFn_hilbertBlockL2ToBlockL2 S] with x hproj hvector hblock
    rw [hvector]
    change ((hilbertBlockSecondProjectionVec.compLpL 2
      (volumeMeasureOn U) S) x).toVec = _
    rw [hproj, hblock]
    simp [hilbertBlockSecondProjectionVec, HilbertBlockVec.flux]
  have hshear := responseShearL2Operator_toBlockL2_ae σ hσ H
    (hilbertPureFirstL2 U p)
  have hmap : hilbertVectorL2ToVectorL2
      (physicalPositiveShear Q σ hσ H p) =
        -hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) := by
    change hilbertVectorL2ToVectorL2 (-(hilbertSecondProjection U S)) = _
    exact map_neg (hilbertVectorL2ToVectorL2 (U := U)) _
  have hneg := MeasureTheory.Lp.coeFn_neg
    (hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S))
  change hilbertVectorL2ToVectorL2 (-(hilbertSecondProjection U S)) =ᵐ[
    volumeMeasureOn U] _
  filter_upwards [hproj, hshear, hinsert, hneg] with x hproj' hshear' hinsert' hnegative
  calc
    hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ H p) x =
        (-hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S)) x :=
      congrArg (fun f : VectorL2 U => f x) hmap
    _ = -hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) x := hnegative
    _ = -((hilbertBlockL2ToBlockL2 S x).2) := by rw [hproj']
    _ = (responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
      have hsecond := congrArg Prod.snd hshear'
      rw [hinsert'] at hsecond
      rw [hsecond]
      simp [responseShearCorrection]

/-- On the actual shell restriction, the insertion shear before the flux
projection is exactly the shell scalar times the rotated H10 source carrier.
The following theorem is the exact source-side operator action. -/
theorem flat_source_positive_shear_actual_shell_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (hQcl : closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀)
    (σ : ℝ) (hσ : 0 < σ)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ))
    (p : (physicalPotentialSpace Q).toSubmodule) :
    hilbertVectorL2ToVectorL2
        (physicalPositiveShear Q σ hσ
          (σ • physicalResponseRestriction Q hQcl z)
          (p : HilbertVectorL2 (openCubeSet Q))) =ᵐ[
            volumeMeasureOn (openCubeSet Q)]
      fun x => z (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) •
        matVecMul responsePlanarJ
          (hilbertVectorL2ToVectorL2 (p : HilbertVectorL2 (openCubeSet Q)) x) := by
  let fresh := physicalResponseRestriction Q hQcl z
  have hshear := physical_positive_shear_to_plain_ae Q σ hσ
    (σ • fresh) (p : HilbertVectorL2 (openCubeSet Q))
  filter_upwards [hshear,
    ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with x hshear' hx
  change (hilbertVectorL2ToVectorL2
      (physicalPositiveShear Q σ hσ (σ • fresh)
        (p : HilbertVectorL2 (openCubeSet Q)))) x = _
  rw [hshear', responseCoefficientExtension_smul_on σ fresh hx,
    responseCoefficientExtension_eq fresh hx]
  have hrestriction : fresh ⟨x, subset_closure hx⟩ =
      z ⟨x, hQcl (subset_closure hx)⟩ := rfl
  rw [hrestriction]
  have hclamp := lambda8CovarianceClamp_eq_of_mem a₀ b₀ c₀ d₀ hab hcd (hQ hx)
  have hsub : (⟨x, hQcl (subset_closure hx)⟩ :
      closedRectangle a₀ b₀ c₀ d₀) =
        lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x := by
    simpa using hclamp.symm
  rw [hsub]
  congr 1
  field_simp [hσ.ne']

/-- The physical insertion's defining action is the flux projection of the
positive shear. The projection is part of the operator. -/
theorem physical_insertion_eq_flux_projected_shear
    (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q))
    (p : (physicalPotentialSpace Q).toSubmodule) :
    physicalProjectedInsertion Q σ hσ H p =
      (physicalFluxSpace Q).toSubmodule.subtypeL
        ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
          (physicalPositiveShear Q σ hσ H (p : HilbertVectorL2 (openCubeSet Q)))) := rfl

/-- The pointwise quarter-turn on the physical vector L² space. It is written
using the already-defined positive physical shear with unit coefficient, so
its action follows from the same operator realization as the source term. -/
noncomputable def rotateVectorL2 (Q : TriadicCube 2) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  physicalPositiveShear Q 1 (by norm_num) 1

/-- The rotation operator acts by the source's quarter-turn matrix. -/
theorem rotate_vectorL2_toPlain_ae
    (Q : TriadicCube 2) (p : HilbertVectorL2 (openCubeSet Q)) :
    hilbertVectorL2ToVectorL2 (rotateVectorL2 Q p) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x => matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
  have h := physical_positive_shear_to_plain_ae Q 1 (by norm_num)
    (1 : ResponseCoefficient (openCubeSet Q)) p
  filter_upwards [h,
    ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with x hx hxQ
  calc
    (hilbertVectorL2ToVectorL2 (rotateVectorL2 Q p)) x =
        ((responseCoefficientExtension
          (1 : ResponseCoefficient (openCubeSet Q))) x / 1) •
          matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
      simpa only [rotateVectorL2] using hx
    _ = matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
      rw [responseCoefficientExtension_eq (U := openCubeSet Q)
        (1 : ResponseCoefficient (openCubeSet Q)) hxQ]
      simp

private theorem flat_source_shell_value_toPlain_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    flatSourceQ3ShellValueLInf Q hab hcd z =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x => z (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) := by
  let μ := volumeMeasureOn (openCubeSet Q)
  let clamp : C(Vec 2, closedRectangle a₀ b₀ c₀ d₀) :=
    ⟨lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd,
      flat_source_clamp_continuous a₀ b₀ c₀ d₀ hab hcd⟩
  let h3ToBounded : C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ]
      BoundedContinuousFunction (closedRectangle a₀ b₀ c₀ d₀) ℝ :=
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closedRectangle a₀ b₀ c₀ d₀) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hbcf : (BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp)
      (h3ToBounded z) =ᵐ[μ]
        (fun x => z (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x)) := by
    filter_upwards [BoundedContinuousFunction.coeFn_toLp (∞ : ℝ≥0∞) μ ℝ
      ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp) (h3ToBounded z))]
      with x hx
    simpa [clamp, h3ToBounded,
      BoundedContinuousFunction.compContinuousCLM_apply] using hx
  have hdef : flatSourceQ3ShellValueLInf Q hab hcd z =
      BoundedContinuousFunction.toLp (∞ : ℝ≥0∞) μ ℝ
        ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ clamp).comp
          h3ToBounded z) := rfl
  rw [hdef]
  exact (BoundedContinuousFunction.coeFn_toLp (∞ : ℝ≥0∞) μ ℝ _).trans hbcf

/-- The actual Wick representative `ψ p` has the expected pointwise
representative on the parent cube. -/
theorem flat_source_wick_toPlain_ae
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (e : Vec 2) (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) :
    hilbertVectorL2ToVectorL2
        (flatSourceQ3ShellProduct Q hab hcd e z) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      fun x => z (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) •
        hilbertVectorL2ToVectorL2
          (flatSourcePotentialCarrier Q hab hcd e z :
            HilbertVectorL2 (openCubeSet Q)) x := by
  let μ := volumeMeasureOn (openCubeSet Q)
  let s := flatSourceQ3ShellValueLInf Q hab hcd z
  let p := (flatSourcePotentialCarrier Q hab hcd e z :
    HilbertVectorL2 (openCubeSet Q))
  have hs := flat_source_shell_value_toPlain_ae Q hab hcd z
  have hp := coeFn_hilbertVectorL2ToVectorL2 (U := openCubeSet Q) p
  have hsmul := Lp.coeFn_lpSMul (r := 2) s p
  have hprod := coeFn_hilbertVectorL2ToVectorL2 (U := openCubeSet Q) (s • p)
  change hilbertVectorL2ToVectorL2 (s • p) =ᵐ[μ] _
  filter_upwards [hprod, hsmul, hs, hp] with x hprod' hsmul' hs' hp'
  calc
    hilbertVectorL2ToVectorL2 (s • p) x = (s x • p x).toVec := by
      rw [hprod']
      have hx : (s • p) x = s x • p x := by
        simpa only [Pi.smul_apply'] using hsmul'
      rw [hx]
    _ = s x • hilbertVectorL2ToVectorL2 p x := by
      rw [hp']
      exact (HilbertVec.continuousLinearEquivVec 2).map_smul _ _
    _ = z (lambda8CovarianceClamp a₀ b₀ c₀ d₀ hab hcd x) •
        hilbertVectorL2ToVectorL2 p x := by rw [hs']

/-- Before the flux projection, the physical insertion is exactly the
quarter-turn of the fixed Wick representative. -/
theorem flat_source_positive_shear_eq_rotated_wick
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (hQcl : closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀)
    (σ : ℝ) (hσ : 0 < σ)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) (e : Vec 2) :
    physicalPositiveShear Q σ hσ
        (σ • physicalResponseRestriction Q hQcl z)
        (flatSourcePotentialCarrier Q hab hcd e z :
          HilbertVectorL2 (openCubeSet Q)) =
      rotateVectorL2 Q (flatSourceQ3ShellProduct Q hab hcd e z) := by
  let p := (flatSourcePotentialCarrier Q hab hcd e z :
    HilbertVectorL2 (openCubeSet Q))
  let W := flatSourceQ3ShellProduct Q hab hcd e z
  have hleft := flat_source_positive_shear_actual_shell_ae Q hab hcd
    hQ hQcl σ hσ z (flatSourcePotentialCarrier Q hab hcd e z)
  have hright := rotate_vectorL2_toPlain_ae Q W
  have hW := flat_source_wick_toPlain_ae Q hab hcd e z
  have hplain :
      hilbertVectorL2ToVectorL2
          (physicalPositiveShear Q σ hσ
            (σ • physicalResponseRestriction Q hQcl z) p) =
        hilbertVectorL2ToVectorL2 (rotateVectorL2 Q W) := by
    apply Lp.ext
    filter_upwards [hleft, hright, hW] with x hleft' hright' hW'
    rw [hleft', hright', hW']
    simp [matVecMul_smul]
  calc
    physicalPositiveShear Q σ hσ
        (σ • physicalResponseRestriction Q hQcl z) p =
        vectorL2ToHilbertVectorL2
          (hilbertVectorL2ToVectorL2
            (physicalPositiveShear Q σ hσ
              (σ • physicalResponseRestriction Q hQcl z) p)) :=
      (vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 _).symm
    _ = vectorL2ToHilbertVectorL2
        (hilbertVectorL2ToVectorL2 (rotateVectorL2 Q W)) :=
      congrArg vectorL2ToHilbertVectorL2 hplain
    _ = rotateVectorL2 Q W :=
      vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 _

/-- The source's flat insertion, including its quarter-turn and flux
projection, is the flux projection of the rotated Wick representative. -/
theorem flat_source_eq_flux_projection_of_rotated_wick
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (hQcl : closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀)
    (σ : ℝ) (hσ : 0 < σ)
    (z : C(closedRectangle a₀ b₀ c₀ d₀, ℝ)) (e : Vec 2) :
    let p := flatSourcePotentialCarrier Q hab hcd e z
    let fresh := physicalResponseRestriction Q hQcl z
    let H := σ • fresh
    let W := flatSourceQ3ShellProduct Q hab hcd e z
    physicalProjectedInsertion Q σ hσ H p =
      (physicalFluxSpace Q).toSubmodule.subtypeL
        ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
          (rotateVectorL2 Q W)) := by
  change (physicalFluxSpace Q).toSubmodule.subtypeL
      ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
        (physicalPositiveShear Q σ hσ
          (σ • physicalResponseRestriction Q hQcl z)
          (flatSourcePotentialCarrier Q hab hcd e z :
            HilbertVectorL2 (openCubeSet Q)))) = _
  rw [flat_source_positive_shear_eq_rotated_wick Q hab hcd hQ hQcl
    σ hσ z e]

end ASDExplicitGamma.Scalar
