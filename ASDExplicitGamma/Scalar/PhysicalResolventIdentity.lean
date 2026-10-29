module

public import ASDExplicitGamma.Scalar.PhysicalPureFluxMinimum
public import ASDExplicitGamma.Scalar.PhysicalResponse
public import ASDExplicitGamma.Variational.AffineGradientClosed
public import Homogenization.Sobolev.PotentialSolenoidalL2Recovery
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization

/-! The physical projected coefficient operator for the old and inserted
skew fields. The zero-normal-trace flux is removed by the orthogonal
projection onto its complement. -/

@[expose] public section

open Homogenization
open ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped InnerProduct InnerProductSpace

namespace ASDExplicitGamma.Scalar

noncomputable section

local instance physicalResolventFiniteMeasure (Q : TriadicCube 2) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The closed zero-trace potential space on the physical response square. -/
noncomputable def physicalPotentialSpace (Q : TriadicCube 2) :
    ClosedSubmodule ℝ (HilbertVectorL2 (openCubeSet Q)) :=
  ⟨PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q),
    potentialZeroTrace_isClosed Q⟩

/-- The zero-normal-trace solenoidal space on the physical response square. -/
noncomputable def physicalSolenoidalSpace (Q : TriadicCube 2) :
    ClosedSubmodule ℝ (HilbertVectorL2 (openCubeSet Q)) :=
  ⟨PotentialSolenoidalExact.solenoidalZeroNormalTrace (openCubeSet Q),
    (PotentialSolenoidalExact.potential (openCubeSet Q)).isClosed_orthogonal⟩

/-- The complementary flux space used after eliminating the solenoidal part. -/
noncomputable def physicalFluxSpace (Q : TriadicCube 2) :
    ClosedSubmodule ℝ (HilbertVectorL2 (openCubeSet Q)) :=
  (physicalSolenoidalSpace Q).orthogonal

/-- Insert a vector field into the first coordinate of the doubled L² carrier. -/
def pureFirst : HilbertVec 2 →ₗᵢ[ℝ] HilbertBlockVec 2 where
  toFun y := PiLp.single 2 0 y
  map_add' _ _ := PiLp.single_add 2 0
  map_smul' c y := by
    apply PiLp.ext
    intro i
    simp only [PiLp.single_apply, PiLp.smul_apply]
    fin_cases i <;> norm_num
  norm_map' y := PiLp.norm_single 2 (fun _ : Fin 2 => HilbertVec 2) 0 y

/-- Insert a vector field into the first coordinate of the doubled L² space. -/
def hilbertPureFirstL2 (U : Set (Vec 2)) :
    HilbertVectorL2 U →L[ℝ] HilbertBlockL2 U :=
  pureFirst.toContinuousLinearMap.compLpL 2 (volumeMeasureOn U)

/-- Project a doubled L² field onto its second vector coordinate. -/
def hilbertBlockSecondProjectionVec :
    HilbertBlockVec 2 →L[ℝ] HilbertVec 2 :=
  PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 1

def hilbertSecondProjection (U : Set (Vec 2)) :
    HilbertBlockL2 U →L[ℝ] HilbertVectorL2 U :=
  hilbertBlockSecondProjectionVec.compLpL 2 (volumeMeasureOn U)

private theorem hilbertSecondProjection_toBlock_ae (U : Set (Vec 2))
    (X : HilbertBlockL2 U) :
    hilbertVectorL2ToVectorL2 (hilbertSecondProjection U X) =ᵐ[volumeMeasureOn U]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2)
      (μ := volumeMeasureOn U)
      (L := hilbertBlockSecondProjectionVec) (f := X),
    coeFn_hilbertVectorL2ToVectorL2 (hilbertSecondProjection U X),
    coeFn_hilbertBlockL2ToBlockL2 X] with x hproj hvector hblock
  rw [hvector]
  change ((hilbertBlockSecondProjectionVec.compLpL 2 (volumeMeasureOn U) X) x).toVec = _
  rw [hproj, hblock]
  simp [hilbertBlockSecondProjectionVec, HilbertBlockVec.flux]

private theorem hilbertBlock_firstInsert_toBlock_ae (U : Set (Vec 2))
    (p : HilbertVectorL2 U) :
    hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p) =ᵐ[volumeMeasureOn U]
      fun x => (hilbertVectorL2ToVectorL2 p x, 0) := by
  filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
      (L := pureFirst.toContinuousLinearMap) (f := p),
    coeFn_hilbertVectorL2ToVectorL2 p] with x hblock hinsert hp
  rw [hblock]
  change ((pureFirst.toContinuousLinearMap.compLpL 2 (volumeMeasureOn U) p) x).toBlockVec = _
  rw [hinsert, hp]
  apply Prod.ext
  · ext i
    simp [pureFirst, HilbertVec.toVec]
  · ext i
    simp [pureFirst, HilbertVec.toVec]

private theorem hilbertVectorL2_norm_sq_integral (U : Set (Vec 2))
    (f : Vec 2 → Vec 2) (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ ^ 2 =
      ∫ x in U, vecNormSq (f x) ∂MeasureTheory.volume := by
  rw [← real_inner_self_eq_norm_sq,
    inner_toHilbertVectorL2OfVecField_eq_integral hf hf]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  simp [vecDot, vecNormSq]

/-- The positive coefficient map `p ↦ (H/σ) J p`, before projection. -/
noncomputable def physicalPositiveShear (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q)) :
    HilbertVectorL2 (openCubeSet Q) →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  -((hilbertSecondProjection (openCubeSet Q)).comp
    ((responseShearL2Operator σ hσ H).comp
      (hilbertPureFirstL2 (openCubeSet Q))))

private theorem physicalPositiveShear_toPlain_ae
    (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q))
    (p : HilbertVectorL2 (openCubeSet Q)) :
    hilbertVectorL2ToVectorL2
        (physicalPositiveShear Q σ hσ H p) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
  let U := openCubeSet Q
  let S := responseShearL2Operator σ hσ H (hilbertPureFirstL2 U p)
  have hp : hilbertBlockL2ToBlockL2 (hilbertPureFirstL2 U p) =ᵐ[volumeMeasureOn U]
      fun x => (hilbertVectorL2ToVectorL2 p x, 0) :=
    hilbertBlock_firstInsert_toBlock_ae U p
  have hS := responseShearL2Operator_toBlockL2_ae σ hσ H (hilbertPureFirstL2 U p)
  have hP := hilbertSecondProjection_toBlock_ae U S
  have hmap : hilbertVectorL2ToVectorL2
      (physicalPositiveShear Q σ hσ H p) =
        -hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) := by
    change hilbertVectorL2ToVectorL2 (-(hilbertSecondProjection U S)) = _
    exact map_neg (hilbertVectorL2ToVectorL2 (U := U)) _
  have hneg := MeasureTheory.Lp.coeFn_neg
    (hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S))
  change hilbertVectorL2ToVectorL2 (-(hilbertSecondProjection U S)) =ᵐ[volumeMeasureOn U] _
  filter_upwards [hP, hS, hp, hneg] with x hproj hshear hinsert hnegative
  calc
    hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ H p) x =
        (-hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S)) x :=
      congrArg (fun f : VectorL2 U => f x) hmap
    _ = -hilbertVectorL2ToVectorL2 (hilbertSecondProjection U S) x := hnegative
    _ = -((hilbertBlockL2ToBlockL2 S x).2) := by rw [hproj]
    _ = (responseCoefficientExtension H x / σ) •
        matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := by
      have hsecond := congrArg Prod.snd hshear
      rw [hinsert] at hsecond
      rw [hsecond]
      simp [responseShearCorrection]

/-- The projected old coefficient from zero-trace potentials to the
complementary flux space, viewed in the ambient vector L² space. -/
noncomputable def physicalProjectedCoefficient (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q)) :
    (physicalPotentialSpace Q).toSubmodule →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
  ((physicalFluxSpace Q).toSubmodule.subtypeL.comp
    ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto)).comp
    ((physicalPositiveShear Q σ hσ k).comp
      (physicalPotentialSpace Q).toSubmodule.subtypeL)

/-- The physical insertion acts on the same old projected Hilbert space. -/
noncomputable def physicalProjectedInsertion (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q)) :
    (physicalPotentialSpace Q).toSubmodule →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
  physicalProjectedCoefficient Q σ hσ H

/-- The constant physical load as an element of the vector L² carrier. -/
noncomputable def physicalConstantLoad (Q : TriadicCube 2) (e : Vec 2) :
    HilbertVectorL2 (openCubeSet Q) :=
  toHilbertVectorL2OfVecField (memVectorL2_const (U := openCubeSet Q) e)

theorem physicalConstantLoad_mem_fluxSpace (Q : TriadicCube 2) (e : Vec 2) :
    physicalConstantLoad Q e ∈ (physicalFluxSpace Q).toSubmodule := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let u : H1Function (openCubeSet Q) :=
    H1Function.affineOnIsSobolevRegularDomain hU.isSobolevRegularDomain e
  have heq : physicalConstantLoad Q e = u.gradToHilbertVectorL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField
        (memVectorL2_const (U := openCubeSet Q) e),
      u.coeFn_gradToHilbertVectorL2] with x hconst hgrad
    change (toHilbertVectorL2OfVecField
      (memVectorL2_const (U := openCubeSet Q) e)) x =
      u.gradToHilbertVectorL2 x
    rw [hconst, hgrad]
    simp only [hilbertifyVecField]
    rw [H1Function.affineOnIsSobolevRegularDomain_grad]
  have hePot : physicalConstantLoad Q e ∈
      PotentialSolenoidalExact.potential (openCubeSet Q) := by
    rw [heq]
    exact ⟨u, rfl⟩
  change physicalConstantLoad Q e ∈
    (PotentialSolenoidalExact.potential (openCubeSet Q))ᗮᗮ
  exact Submodule.le_orthogonal_orthogonal _ hePot

/-- Orthogonally eliminate a closed solenoidal correction from a residual.
The minimizing correction is the solenoidal projection of the shear term. -/
theorem orthogonalProjection_eliminates {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : ClosedSubmodule ℝ H) (e w : H) (he : e ∈ K.toSubmoduleᗮ) :
    ∃ s : K.toSubmodule,
      e + (s : H) - w = e - (K.toSubmoduleᗮ.orthogonalProjectionOnto w : H) ∧
      ∀ q : K.toSubmodule,
        ‖e - (K.toSubmoduleᗮ.orthogonalProjectionOnto w : H)‖ ≤
          ‖e + (q : H) - w‖ := by
  let pY := K.toSubmoduleᗮ.orthogonalProjectionOnto
  let s : K.toSubmodule := K.toSubmodule.orthogonalProjectionOnto w
  have heY : pY e = ⟨e, he⟩ := by
    apply Subtype.ext
    change K.toSubmoduleᗮ.starProjection e = e
    exact K.toSubmoduleᗮ.starProjection_eq_self_iff.mpr he
  have hsDecomp : w = (pY w : H) + (s : H) := by
    have h : (pY w : H) = w - (s : H) := by
      change K.toSubmoduleᗮ.starProjection w =
        w - K.toSubmodule.starProjection w
      exact K.toSubmodule.starProjection_orthogonal_val w
    calc
      w = (w - (s : H)) + (s : H) := by abel
      _ = (pY w : H) + (s : H) := by rw [← h]
  have hEq : e + (s : H) - w = e - (pY w : H) := by
    calc
      e + (s : H) - w =
          e + (s : H) - ((pY w : H) + (s : H)) := by
            exact congrArg (fun z : H => e + (s : H) - z) hsDecomp
      _ = e - (pY w : H) := by abel
  refine ⟨s, hEq, ?_⟩
  intro q
  have hqmem : (q : H) ∈ (K.toSubmoduleᗮ)ᗮ :=
    K.toSubmodule.le_orthogonal_orthogonal q.property
  have hpq : pY q = 0 :=
    K.toSubmoduleᗮ.orthogonalProjectionOnto_apply_of_mem_orthogonal hqmem
  have hResidual :
      (pY (e + (q : H) - w) : H) = e - (pY w : H) := by
    have hlinear : pY (e + (q : H) - w) = pY e + pY q - pY w := by
      rw [map_sub, map_add]
    rw [hlinear]
    change (pY e + pY q - pY w : H) = e - (pY w : H)
    rw [heY, hpq]
    simp
  calc
    ‖e - (pY w : H)‖ = ‖pY (e + (q : H) - w)‖ := by
      rw [← hResidual]
      rfl
    _ ≤ ‖e + (q : H) - w‖ := K.toSubmoduleᗮ.norm_orthogonalProjectionOnto_apply_le _

/-- At a fixed physical coefficient, minimizing the flux correction in the
actual L² energy is exactly the complementary projection used by the pure
flux resolvent. -/
theorem physicalProjectedCoefficient_eliminatesSolenoidal
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (x : (physicalPotentialSpace Q).toSubmodule) :
    ∃ s : (physicalSolenoidalSpace Q).toSubmodule,
      pureFluxEnergy (ν / σ)
          (physicalProjectedCoefficient Q σ hσ k)
          (physicalConstantLoad Q e) x =
        (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ *
          ‖physicalConstantLoad Q e + (s : HilbertVectorL2 (openCubeSet Q)) -
            physicalPositiveShear Q σ hσ k (x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 ∧
      ∀ q : (physicalSolenoidalSpace Q).toSubmodule,
        pureFluxEnergy (ν / σ)
            (physicalProjectedCoefficient Q σ hσ k)
            (physicalConstantLoad Q e) x ≤
          (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ *
            ‖physicalConstantLoad Q e + (q : HilbertVectorL2 (openCubeSet Q)) -
              physicalPositiveShear Q σ hσ k (x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 := by
  let K := physicalSolenoidalSpace Q
  let W := physicalPositiveShear Q σ hσ k
  let G := K.toSubmoduleᗮ.orthogonalProjectionOnto
  let A := physicalProjectedCoefficient Q σ hσ k
  let eH := physicalConstantLoad Q e
  have he : eH ∈ K.toSubmoduleᗮ := by
    simpa [K, eH, physicalFluxSpace] using
      physicalConstantLoad_mem_fluxSpace Q e
  obtain ⟨s, hs, hmin⟩ := orthogonalProjection_eliminates K eH
    (W (x : HilbertVectorL2 (openCubeSet Q))) he
  have hA : A x = (G (W (x : HilbertVectorL2 (openCubeSet Q))) :
      HilbertVectorL2 (openCubeSet Q)) := rfl
  have hA' : eH - A x = eH - (G (W (x : HilbertVectorL2 (openCubeSet Q))) :
      HilbertVectorL2 (openCubeSet Q)) := by rw [hA]
  refine ⟨s, ?_, ?_⟩
  · change (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ * ‖eH - A x‖ ^ 2 = _
    rw [hA', ← hs]
  · intro q
    change (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ * ‖eH - A x‖ ^ 2 ≤
      (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ *
        ‖eH + (q : HilbertVectorL2 (openCubeSet Q)) - W
          (x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2
    rw [hA']
    have hn := hmin q
    have hnSq : ‖eH - (G (W (x : HilbertVectorL2 (openCubeSet Q))) :
        HilbertVectorL2 (openCubeSet Q))‖ ^ 2 ≤
        ‖eH + (q : HilbertVectorL2 (openCubeSet Q)) -
          W (x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
    calc
      (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ *
          ‖eH - (G (W (x : HilbertVectorL2 (openCubeSet Q))) :
            HilbertVectorL2 (openCubeSet Q))‖ ^ 2 =
        (ν / σ)⁻¹ *
          ‖eH - (G (W (x : HilbertVectorL2 (openCubeSet Q))) :
            HilbertVectorL2 (openCubeSet Q))‖ ^ 2 + (ν / σ) * ‖x‖ ^ 2 := by ring
      _ ≤ (ν / σ)⁻¹ *
          ‖eH + (q : HilbertVectorL2 (openCubeSet Q)) -
            W (x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 + (ν / σ) * ‖x‖ ^ 2 :=
          by
            nlinarith [mul_le_mul_of_nonneg_left hnSq
              (inv_nonneg.mpr (div_nonneg hν.le hσ.le))]
      _ = (ν / σ) * ‖x‖ ^ 2 + (ν / σ)⁻¹ *
          ‖eH + (q : HilbertVectorL2 (openCubeSet Q)) -
            W (x : HilbertVectorL2 (openCubeSet Q))‖ ^ 2 := by ring

theorem physicalPositiveShear_add (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ)
    (H K : ResponseCoefficient (openCubeSet Q)) :
    physicalPositiveShear Q σ hσ (H + K) =
      physicalPositiveShear Q σ hσ H + physicalPositiveShear Q σ hσ K := by
  apply ContinuousLinearMap.ext
  intro x
  let P := hilbertSecondProjection (openCubeSet Q)
  let I := hilbertPureFirstL2 (openCubeSet Q)
  change -(P ((responseShearL2Operator σ hσ (H + K)) (I x))) =
      -(P ((responseShearL2Operator σ hσ H) (I x))) +
        -(P ((responseShearL2Operator σ hσ K) (I x)))
  rw [responseShearL2Operator_add
    (measurableSet_openCubeSet Q) σ hσ H K, add_apply, map_add]
  abel

theorem physicalProjectedCoefficient_add (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet Q)) :
    physicalProjectedCoefficient Q σ hσ (k + H) =
      physicalProjectedCoefficient Q σ hσ k +
        physicalProjectedInsertion Q σ hσ H := by
  apply ContinuousLinearMap.ext
  intro x
  let G := (physicalFluxSpace Q).toSubmodule.subtypeL.comp
    ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto)
  let I := (physicalPotentialSpace Q).toSubmodule.subtypeL
  change G (physicalPositiveShear Q σ hσ (k + H) (I x)) =
      G (physicalPositiveShear Q σ hσ k (I x)) +
        G (physicalPositiveShear Q σ hσ H (I x))
  rw [physicalPositiveShear_add]
  exact map_add G _ _

private theorem toHilbertVectorL2OfVecField_hilbertVectorL2ToVectorL2
    {U : Set (Vec 2)} (p : HilbertVectorL2 U) :
    toHilbertVectorL2OfVecField
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 p)) = p := by
  let f := hilbertVectorL2ToVectorL2 p
  let hf : MemVectorL2 U f := MeasureTheory.Lp.memLp f
  calc
    toHilbertVectorL2OfVecField hf =
        vectorL2ToHilbertVectorL2 (toVectorL2 hf) :=
          (vectorL2ToHilbertVectorL2_toVectorL2 hf).symm
    _ = vectorL2ToHilbertVectorL2 (hilbertVectorL2ToVectorL2 p) := by
      congr 1
      exact MeasureTheory.Lp.toLp_coeFn (hilbertVectorL2ToVectorL2 p)
        (MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 p))
    _ = p := vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 p

private theorem physicalField_memPotentialSpace
    (Q : TriadicCube 2) {f : Vec 2 → Vec 2}
    (hf : MemVectorL2 (openCubeSet Q) f)
    (hpot : IsPotentialZeroTraceOn (openCubeSet Q) f) :
    toHilbertVectorL2OfVecField hf ∈
      (physicalPotentialSpace Q).toSubmodule := by
  change toHilbertVectorL2OfVecField hf ∈
    PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q)
  rw [PotentialSolenoidalExact.mem_potentialZeroTrace_iff]
  rcases hpot with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hf,
    u.toH1Function.coeFn_gradToHilbertVectorL2] with x hfield hgrad
  rw [hfield, hgrad]
  simp [hilbertifyVecField, ← hu]

private theorem physicalField_memSolenoidalSpace
    (Q : TriadicCube 2) {g : Vec 2 → Vec 2}
    (hg : MemVectorL2 (openCubeSet Q) g)
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g) :
    toHilbertVectorL2OfVecField hg ∈
      (physicalSolenoidalSpace Q).toSubmodule := by
  change toHilbertVectorL2OfVecField hg ∈
    PotentialSolenoidalExact.solenoidalZeroNormalTrace (openCubeSet Q)
  rw [PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff]
  intro u
  rw [show u.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl]
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hg u.grad_memVectorL2]
  exact hsol u

private theorem hilbertBlockOfBlockField_toBlock_ae
    {U : Set (Vec 2)} {F : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 U F) :
    hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF) =ᵐ[volumeMeasureOn U] F := by
  filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF),
    coeFn_toHilbertBlockL2OfBlockField hF] with x htransport hfield
  calc
    hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfBlockField hF) x =
        ((toHilbertBlockL2OfBlockField hF) x).toBlockVec := htransport
    _ = F x := by rw [hfield]; simp [hilbertifyBlockField]

private theorem physicalActualPairEnergy_eq_pureFluxEnergy
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (f g : Vec 2 → Vec 2) (hf : MemVectorL2 (openCubeSet Q) f)
    (hg : MemVectorL2 (openCubeSet Q) g)
    (X : HilbertBlockL2 (openCubeSet Q))
    (hXae : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (f x, e + g x)) :
    (let U := openCubeSet Q
     let p := toHilbertVectorL2OfVecField hf
     let q := toHilbertVectorL2OfVecField hg
     let M := responseFrameMuOperatorSystemData
       (measurableSet_openCubeSet Q)
       (by
         rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
         exact cubeVolume_pos Q)
       ν σ hν hσ k |>.toMuHilbertRealization
     M.energyBilin X X =
       (MeasureTheory.volume U).toReal⁻¹ *
         ((ν / σ) * ‖p‖ ^ 2 + (ν / σ)⁻¹ *
           ‖physicalConstantLoad Q e + q -
             physicalPositiveShear Q σ hσ k p‖ ^ 2)) := by
  let U := openCubeSet Q
  let hU : MeasurableSet U := measurableSet_openCubeSet Q
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    dsimp [U]
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let p := toHilbertVectorL2OfVecField hf
  let q := toHilbertVectorL2OfVecField hg
  let hc : MemVectorL2 U (fun _ => e) := memVectorL2_const e
  let hconst : Vec 2 → Vec 2 := fun _ => e
  let hsum : MemVectorL2 U (hconst + g) := hc.add hg
  let hwLp := hilbertVectorL2ToVectorL2
    (physicalPositiveShear Q σ hσ k p)
  let wField : Vec 2 → Vec 2 := fun x => hwLp x
  let hw : MemVectorL2 U wField := by
    change MeasureTheory.MemLp (fun x => hwLp x) 2 (volumeMeasureOn U)
    exact MeasureTheory.Lp.memLp hwLp
  let hr : MemVectorL2 U (hconst + g - wField) := hsum.sub hw
  have hW : toHilbertVectorL2OfVecField hw =
      physicalPositiveShear Q σ hσ k p := by
    calc
      toHilbertVectorL2OfVecField hw =
          vectorL2ToHilbertVectorL2 (toVectorL2 hw) :=
            (vectorL2ToHilbertVectorL2_toVectorL2 hw).symm
      _ = vectorL2ToHilbertVectorL2 hwLp := by
        rw [show toVectorL2 hw = hwLp from MeasureTheory.Lp.toLp_coeFn hwLp hw]
      _ = physicalPositiveShear Q σ hσ k p :=
        vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 _
  have hR : toHilbertVectorL2OfVecField hr =
      physicalConstantLoad Q e + q -
        physicalPositiveShear Q σ hσ k p := by
    calc
      toHilbertVectorL2OfVecField hr =
          toHilbertVectorL2OfVecField hsum - toHilbertVectorL2OfVecField hw :=
            toHilbertVectorL2OfVecField_sub hsum hw
      _ = (toHilbertVectorL2OfVecField hc +
            toHilbertVectorL2OfVecField hg) -
          physicalPositiveShear Q σ hσ k p := by
            rw [toHilbertVectorL2OfVecField_add hc hg, hW]
      _ = physicalConstantLoad Q e + q -
          physicalPositiveShear Q σ hσ k p := rfl
  have hpPlain : hilbertVectorL2ToVectorL2 p =ᵐ[volumeMeasureOn U] f := by
    rw [show p = toHilbertVectorL2OfVecField hf from rfl,
      hilbertVectorL2ToVectorL2_toHilbertVectorL2 hf]
    exact coeFn_toVectorL2 hf
  have hWPlain := physicalPositiveShear_toPlain_ae Q σ hσ k p
  have hDensity :
    (fun x => responseFrameEnergyDensity ν σ
        (responseCoefficientExtension k x)
        (hilbertBlockL2ToBlockL2 X x)) =ᵐ[volumeMeasureOn U]
        fun x => (ν / σ) * vecNormSq (f x) +
          (ν / σ)⁻¹ * vecNormSq ((hconst + g - wField) x) := by
    filter_upwards [hXae, hWPlain, hpPlain] with x hX hxW hxp
    rw [hX]
    simp only [responseFrameEnergyDensity]
    have hWf : wField x =
        ((responseCoefficientExtension k x / σ) •
          matVecMul responsePlanarJ (f x)) := by
      calc
        wField x = (responseCoefficientExtension k x / σ) •
            matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := hxW
        _ = (responseCoefficientExtension k x / σ) •
            matVecMul responsePlanarJ (f x) := by rw [hxp]
    rw [← hWf]
    have hcoeff : σ / ν = (ν / σ)⁻¹ := by
      field_simp [hν.ne', hσ.ne']
    rw [hcoeff]
    simp [hconst, wField, Pi.add_apply, Pi.sub_apply]
  have hfSqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (f x)) U := by
    simpa [vecNormSq, MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (integrableOn_vecDot_of_memVectorL2 hf hf)
  have hrSqInt : MeasureTheory.IntegrableOn
      (fun x => vecNormSq ((hconst + g - wField) x)) U := by
    simpa [vecNormSq, MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (integrableOn_vecDot_of_memVectorL2 hr hr)
  have hfirstInt : MeasureTheory.Integrable
      (fun x => (ν / σ) * vecNormSq (f x)) (volumeMeasureOn U) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hfSqInt.const_mul (ν / σ)
  have hsecondInt : MeasureTheory.Integrable
      (fun x => (ν / σ)⁻¹ * vecNormSq ((hconst + g - wField) x))
        (volumeMeasureOn U) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      hrSqInt.const_mul ((ν / σ)⁻¹)
  have hIntegral :
      ∫ x in U, responseFrameEnergyDensity ν σ
          (responseCoefficientExtension k x) (hilbertBlockL2ToBlockL2 X x)
          ∂MeasureTheory.volume =
        (ν / σ) * ‖p‖ ^ 2 + (ν / σ)⁻¹ * ‖toHilbertVectorL2OfVecField hr‖ ^ 2 := by
    rw [MeasureTheory.integral_congr_ae hDensity]
    rw [MeasureTheory.integral_add hfirstInt hsecondInt]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      ← hilbertVectorL2_norm_sq_integral U f hf,
      ← hilbertVectorL2_norm_sq_integral U
        (fun x => (hconst + g - wField) x) hr]
  change M.energyBilin X X = _
  rw [responseFrameMu_energy_eq_volumeAverage_density hU hvol ν σ hν hσ k X]
  unfold volumeAverage
  rw [hIntegral, hR]

private theorem physical_response_eq_pureFlux_inverse
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) k =
      (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        pureFluxInverseQuadratic (ν / σ) (div_pos hν hσ)
          (physicalProjectedCoefficient Q σ hσ k)
          (physicalConstantLoad Q e) := by
  let U := openCubeSet Q
  let hU : MeasurableSet U := measurableSet_openCubeSet Q
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    dsimp [U]
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  let α := ν / σ
  have hα : 0 < α := div_pos hν hσ
  let A := physicalProjectedCoefficient Q σ hσ k
  let eH := physicalConstantLoad Q e
  let P : BlockVec 2 := (0, e)
  let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  obtain ⟨x, hxValue, hxMinimum⟩ :=
    pureFlux_block_inverse_minimizes hα A eH
  obtain ⟨s, hsValue, hsMinimum⟩ :=
    physicalProjectedCoefficient_eliminatesSolenoidal Q ν σ hν hσ k e x
  rcases (PotentialSolenoidalExact.mem_potentialZeroTrace_iff
      (x : HilbertVectorL2 U)).1 x.2 with ⟨u, hu⟩
  let f : Vec 2 → Vec 2 := u.toH1Function.grad
  let hf : MemVectorL2 U f := u.toH1Function.grad_memVectorL2
  have hfx : toHilbertVectorL2OfVecField hf = (x : HilbertVectorL2 U) := by
    change u.toH1Function.gradToHilbertVectorL2 = (x : HilbertVectorL2 U)
    exact hu
  have hpot : IsPotentialZeroTraceOn U f := u.isPotentialZeroTraceOn
  let g : Vec 2 → Vec 2 := hilbertVectorL2ToVectorL2 (s : HilbertVectorL2 U)
  let hg : MemVectorL2 U g := by
    change MeasureTheory.MemLp
      (fun y => hilbertVectorL2ToVectorL2 (s : HilbertVectorL2 U) y)
      2 (volumeMeasureOn U)
    exact MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (s : HilbertVectorL2 U))
  have hgs : toHilbertVectorL2OfVecField hg = (s : HilbertVectorL2 U) := by
    simpa [g, hg] using
      (toHilbertVectorL2OfVecField_hilbertVectorL2ToVectorL2
        (s : HilbertVectorL2 U))
  have hsol : IsSolenoidalZeroNormalTraceOn U g := by
    intro φ
    have horth :=
      (PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff
        (s : HilbertVectorL2 U)).1 s.2 φ
    have hinner := inner_toHilbertVectorL2OfVecField_eq_integral hg φ.grad_memVectorL2
    calc
      ∫ y in U, vecDot (g y) (φ.grad y) ∂MeasureTheory.volume =
          inner ℝ (toHilbertVectorL2OfVecField hg)
            (toHilbertVectorL2OfVecField φ.grad_memVectorL2) := hinner.symm
      _ = 0 := by
        rw [hgs, ← show φ.gradToHilbertVectorL2 =
          toHilbertVectorL2OfVecField φ.grad_memVectorL2 from rfl]
        exact horth
  let state : BlockState 2 := ⟨f, fun y => e + g y⟩
  have hAdm : IsBlockMuAdmissible U P state := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [state, P] using hf
    · simpa [state, P] using hpot
    · simpa [state, P, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg
    · simpa [state, P, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsol
  let X := toHilbertBlockL2OfBlockField hAdm.memBlockL2_eval
  have hXae : hilbertBlockL2ToBlockL2 X =ᵐ[volumeMeasureOn U]
      fun y => (f y, e + g y) := by
    have h := hilbertBlockOfBlockField_toBlock_ae hAdm.memBlockL2_eval
    filter_upwards [h] with y hy
    simpa [BlockState.eval, state] using hy
  have hEnergyBase := physicalActualPairEnergy_eq_pureFluxEnergy
    Q ν σ hν hσ k e f g hf hg X hXae
  have hEnergyPair : M.energyBilin X X = (MeasureTheory.volume U).toReal⁻¹ *
      (α * ‖x‖ ^ 2 + α⁻¹ *
        ‖eH + (s : HilbertVectorL2 U) -
          physicalPositiveShear Q σ hσ k (x : HilbertVectorL2 U)‖ ^ 2) := by
    simpa [M, U, α, hfx, hgs] using hEnergyBase
  have hEnergy : M.energyBilin X X =
      (MeasureTheory.volume U).toReal⁻¹ * pureFluxEnergy α A eH x := by
    calc
      M.energyBilin X X = (MeasureTheory.volume U).toReal⁻¹ *
          (α * ‖x‖ ^ 2 + α⁻¹ *
            ‖eH + (s : HilbertVectorL2 U) -
              physicalPositiveShear Q σ hσ k (x : HilbertVectorL2 U)‖ ^ 2) := hEnergyPair
      _ = (MeasureTheory.volume U).toReal⁻¹ * pureFluxEnergy α A eH x := by
        rw [← hsValue]
  have hResponseTwo :
      responseFrameEnergyObservable hU hvol ν σ hν hσ P k = 2 * M.muCandidate P := by
    change 2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (0 + k)).toMuHilbertRealization.muCandidate P =
      2 * M.muCandidate P
    rw [zero_add]
  have hResponseEnergy :
      responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
        M.energyBilin (M.minimizerMap P) (M.minimizerMap P) := by
    calc
      responseFrameEnergyObservable hU hvol ν σ hν hσ P k = 2 * M.muCandidate P :=
        hResponseTwo
      _ = M.energyBilin (M.minimizerMap P) (M.minimizerMap P) := by
        change 2 * quadraticEnergy M.energyBilin (M.minimizerMap P) = _
        simp [quadraticEnergy]
  have hCorrection :
      X - M.constantField P ∈ M.correctionSpace.correctionSpace := by
    have hsplit := hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    rw [show X = toHilbertBlockL2OfBlockField hAdm.memBlockL2_eval from rfl, hsplit]
    change (blockVecToHilbertBlockL2Const (U := U) P +
        hAdm.toCorrectionFieldDataOfAdmissible.toHilbertBlockL2) -
        blockVecToHilbertBlockL2Const (U := U) P ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData.correctionSpace
    rw [add_sub_cancel_left]
    exact hAdm.toCorrectionFieldData_mem_correctionSpace
  have hMinimum := M.muCandidate_le_quadraticEnergy P X hCorrection
  have hTwiceMinimum : 2 * M.muCandidate P ≤ M.energyBilin X X := by
    calc
      2 * M.muCandidate P = 2 * quadraticEnergy M.energyBilin (M.minimizerMap P) := by
        rfl
      _ ≤ 2 * quadraticEnergy M.energyBilin X :=
        mul_le_mul_of_nonneg_left hMinimum (by norm_num)
      _ = M.energyBilin X X := by simp [quadraticEnergy]
  have hUpper : responseFrameEnergyObservable hU hvol ν σ hν hσ P k ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        pureFluxInverseQuadratic α hα A eH := by
    calc
      responseFrameEnergyObservable hU hvol ν σ hν hσ P k = 2 * M.muCandidate P :=
        hResponseTwo
      _ ≤ M.energyBilin X X := hTwiceMinimum
      _ = (MeasureTheory.volume U).toReal⁻¹ * pureFluxEnergy α A eH x := hEnergy
      _ = (MeasureTheory.volume U).toReal⁻¹ *
          pureFluxInverseQuadratic α hα A eH := by rw [hxValue]

  let realization := potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
    (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet Q))
  let recovery := realization.toMuCorrectionSpaceRecoveryData
  let correction : recovery.correctionSpace.toSubmodule :=
    ⟨M.minimizerMap P - M.constantField P, M.sub_minimizerMap_apply_mem P⟩
  let data := recovery.repr correction
  have hData : data.toHilbertBlockL2 = M.minimizerMap P - M.constantField P :=
    recovery.repr_eq correction
  let f₀ : Vec 2 → Vec 2 := data.potential
  let g₀ : Vec 2 → Vec 2 := data.flux
  have hf₀ : MemVectorL2 U f₀ := data.potential_memL2
  have hg₀ : MemVectorL2 U g₀ := data.flux_memL2
  have hpot₀ : IsPotentialZeroTraceOn U f₀ := data.isPotentialZeroTrace
  have hsol₀ : IsSolenoidalZeroNormalTraceOn U g₀ := data.isSolenoidalZeroNormalTrace
  have hp₀ : toHilbertVectorL2OfVecField hf₀ ∈
      (physicalPotentialSpace Q).toSubmodule :=
    physicalField_memPotentialSpace Q hf₀ hpot₀
  have hq₀ : toHilbertVectorL2OfVecField hg₀ ∈
      (physicalSolenoidalSpace Q).toSubmodule :=
    physicalField_memSolenoidalSpace Q hg₀ hsol₀
  let x₀ : (physicalPotentialSpace Q).toSubmodule :=
    ⟨toHilbertVectorL2OfVecField hf₀, hp₀⟩
  let q₀ : (physicalSolenoidalSpace Q).toSubmodule :=
    ⟨toHilbertVectorL2OfVecField hg₀, hq₀⟩
  let state₀ : BlockState 2 := ⟨f₀, fun y => e + g₀ y⟩
  have hAdm₀ : IsBlockMuAdmissible U P state₀ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [state₀, P] using hf₀
    · simpa [state₀, P] using hpot₀
    · simpa [state₀, P, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg₀
    · simpa [state₀, P, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsol₀
  let X₀ := toHilbertBlockL2OfBlockField hAdm₀.memBlockL2_eval
  have hX₀ae : hilbertBlockL2ToBlockL2 X₀ =ᵐ[volumeMeasureOn U]
      fun y => (f₀ y, e + g₀ y) := by
    have h := hilbertBlockOfBlockField_toBlock_ae hAdm₀.memBlockL2_eval
    filter_upwards [h] with y hy
    simpa [BlockState.eval, state₀] using hy
  have hEnergy₀Base := physicalActualPairEnergy_eq_pureFluxEnergy
    Q ν σ hν hσ k e f₀ g₀ hf₀ hg₀ X₀ hX₀ae
  have hEnergy₀ : M.energyBilin X₀ X₀ = (MeasureTheory.volume U).toReal⁻¹ *
      (α * ‖toHilbertVectorL2OfVecField hf₀‖ ^ 2 + α⁻¹ *
        ‖eH + toHilbertVectorL2OfVecField hg₀ -
          physicalPositiveShear Q σ hσ k
            (toHilbertVectorL2OfVecField hf₀)‖ ^ 2) := by
    simpa [M, U, α, eH] using hEnergy₀Base
  have hResponse₀ :
      responseFrameEnergyObservable hU hvol ν σ hν hσ P k =
        M.energyBilin X₀ X₀ := by
    rw [hResponseEnergy]
    have hX₀ : X₀ = M.minimizerMap P := by
      calc
        X₀ = blockVecToHilbertBlockL2Const (U := U) P +
            (hAdm₀.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 :=
          hAdm₀.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
        _ = blockVecToHilbertBlockL2Const (U := U) P + data.toHilbertBlockL2 := by
          congr 1
          apply MeasureTheory.Lp.ext
          filter_upwards [(hAdm₀.toCorrectionFieldDataOfAdmissible).coeFn_toHilbertBlockL2,
            data.coeFn_toHilbertBlockL2] with y hleft hright
          rw [hleft, hright]
          simp [f₀, g₀, state₀, P,
            IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible, hilbertBlockField,
            hilbertifyBlockField, blockField, sub_eq_add_neg, add_assoc]
        _ = M.constantField P +
            (M.minimizerMap P - M.constantField P) := by rw [hData]; rfl
        _ = M.minimizerMap P := by abel
    rw [hX₀]
  have hProjection₀ :=
    physicalProjectedCoefficient_eliminatesSolenoidal Q ν σ hν hσ k e x₀
  obtain ⟨s₀, hProjectionValue₀, hProjectionMinimum₀⟩ := hProjection₀
  have hPureLower :
      pureFluxInverseQuadratic α hα A eH ≤ pureFluxEnergy α A eH x₀ := by
    calc
      pureFluxInverseQuadratic α hα A eH = pureFluxEnergy α A eH x := hxValue.symm
      _ ≤ pureFluxEnergy α A eH x₀ := hxMinimum x₀
  have hProjLower : pureFluxEnergy α A eH x₀ ≤
      α * ‖toHilbertVectorL2OfVecField hf₀‖ ^ 2 + α⁻¹ *
        ‖eH + toHilbertVectorL2OfVecField hg₀ -
          physicalPositiveShear Q σ hσ k
            (toHilbertVectorL2OfVecField hf₀)‖ ^ 2 := by
    simpa [α, A, eH, x₀, q₀, pureFluxEnergy] using hProjectionMinimum₀ q₀
  have hPureLowerScaled := mul_le_mul_of_nonneg_left hPureLower
    (inv_nonneg.mpr hvol.le)
  have hPairLowerScaled := mul_le_mul_of_nonneg_left hProjLower
    (inv_nonneg.mpr hvol.le)
  have hLower : (MeasureTheory.volume U).toReal⁻¹ *
      pureFluxInverseQuadratic α hα A eH ≤
        responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
    calc
      (MeasureTheory.volume U).toReal⁻¹ *
          pureFluxInverseQuadratic α hα A eH ≤
        (MeasureTheory.volume U).toReal⁻¹ * pureFluxEnergy α A eH x₀ :=
          hPureLowerScaled
      _ ≤ (MeasureTheory.volume U).toReal⁻¹ *
          (α * ‖toHilbertVectorL2OfVecField hf₀‖ ^ 2 + α⁻¹ *
            ‖eH + toHilbertVectorL2OfVecField hg₀ -
              physicalPositiveShear Q σ hσ k
                (toHilbertVectorL2OfVecField hf₀)‖ ^ 2) := hPairLowerScaled
      _ = M.energyBilin X₀ X₀ := by
        simpa [α, eH] using hEnergy₀.symm
      _ = responseFrameEnergyObservable hU hvol ν σ hν hσ P k := hResponse₀.symm
  apply le_antisymm hUpper hLower

private theorem pureFluxOperator_parityAdjoint {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (α : ℝ) (A : X →L[ℝ] Y) :
    (pureFluxBlockOperator α A).adjoint *
        pureFluxParity (Y := Y) (X := X) =
      pureFluxParity (Y := Y) (X := X) *
        pureFluxBlockOperator α A := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro w
  change ⟪(pureFluxBlockOperator α A).adjoint
      (pureFluxParity z), w⟫_ℝ =
    ⟪pureFluxParity (pureFluxBlockOperator α A z), w⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    pureFluxParity_apply, pureFluxBlockOperator_apply,
    pureFluxParity_apply, pureFluxBlockOperator_apply]
  have hadj₁ : ⟪z.ofLp.1, A w.ofLp.2⟫_ℝ =
      ⟪A.adjoint z.ofLp.1, w.ofLp.2⟫_ℝ :=
    (ContinuousLinearMap.adjoint_inner_left A w.ofLp.2 z.ofLp.1).symm
  have hadj₂ : ⟪z.ofLp.2, A.adjoint w.ofLp.1⟫_ℝ =
      ⟪A z.ofLp.2, w.ofLp.1⟫_ℝ := by
    calc
      ⟪z.ofLp.2, A.adjoint w.ofLp.1⟫_ℝ =
          ⟪A.adjoint w.ofLp.1, z.ofLp.2⟫_ℝ := real_inner_comm _ _
      _ = ⟪w.ofLp.1, A z.ofLp.2⟫_ℝ :=
        ContinuousLinearMap.adjoint_inner_left A z.ofLp.2 w.ofLp.1
      _ = ⟪A z.ofLp.2, w.ofLp.1⟫_ℝ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_neg_left, inner_neg_right,
    starRingEnd_apply, star_trivial]
  simp only [neg_neg, mul_neg, neg_add]
  rw [hadj₁, hadj₂]
  ring

/-- The exact finite-amplitude four-term identity for the physical projected
response, before applying any Gaussian sign cancellation. -/
theorem pureFlux_block_resolvent_identity {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    {α : ℝ} (hα : 0 < α) (A V : X →L[ℝ] Y) (e : Y) :
    let C := pureFluxBlockOperator 0 V
    let B := pureFluxBlockInverse α hα A
    let N := pureFluxBlockInverse α hα (A + V)
    let J := pureFluxParity (Y := Y) (X := X)
    let f := pureFluxLoad (Y := Y) (X := X) e
    let u := B f
    let s := (C * B * C) u
    pureFluxInverseQuadratic α hα (A + V) e -
      pureFluxInverseQuadratic α hα A e =
      -⟪J u, C u⟫_ℝ + ⟪J u, (C * B * C) u⟫_ℝ -
        ⟪J u, (C * B * C * B * C) u⟫_ℝ + ⟪J s, N s⟫_ℝ := by
  let M := pureFluxBlockOperator α A
  let C := pureFluxBlockOperator 0 V
  let B := pureFluxBlockInverse α hα A
  let N := pureFluxBlockInverse α hα (A + V)
  let J := pureFluxParity (Y := Y) (X := X)
  let f := pureFluxLoad (Y := Y) (X := X) e
  have hM : M.adjoint * J = J * M := pureFluxOperator_parityAdjoint α A
  have hC : C.adjoint * J = J * C := pureFluxOperator_parityAdjoint 0 V
  have hBM : B * M = 1 := pureFluxBlockInverse_right α hα A
  have hMB : M * B = 1 := pureFluxBlockInverse_left α hα A
  have hMN : (M + C) * N = 1 := by
    change (pureFluxBlockOperator α A +
      pureFluxBlockOperator 0 V) *
        pureFluxBlockInverse α hα (A + V) = 1
    rw [pureFluxBlockOperator_add]
    exact pureFluxBlockInverse_left α hα (A + V)
  have hNM : N * (M + C) = 1 := by
    change pureFluxBlockInverse α hα (A + V) *
      (pureFluxBlockOperator α A +
        pureFluxBlockOperator 0 V) = 1
    rw [pureFluxBlockOperator_add]
    exact pureFluxBlockInverse_right α hα (A + V)
  have hf : J f = f := by
    simp [J, f, pureFluxParity, pureFluxLoad]
  have h := resolvent_four_term_hilbert_pairing M C B N J
    hM hC hBM hMB hMN hNM f hf
  simpa [pureFluxInverseQuadratic, M, C, B, N, J, f] using h

/-- The pathwise four-term resolvent identity for the actual physical response
observable, with the response normalized by the volume of its square. The
fields `k` and `H` are the OLD bounded skew coefficient and its physical
insertion; the fixed frame scale `σ` is unchanged across the insertion. -/
theorem physicalResponse_fourTerm_identity
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let U := openCubeSet Q
    let α := ν / σ
    let hα := div_pos hν hσ
    let X := (physicalPotentialSpace Q).toSubmodule
    let Y := HilbertVectorL2 U
    let A : X →L[ℝ] Y := physicalProjectedCoefficient Q σ hσ k
    let V : X →L[ℝ] Y := physicalProjectedInsertion Q σ hσ H
    let C := pureFluxBlockOperator 0 V
    let B := pureFluxBlockInverse α hα A
    let N := pureFluxBlockInverse α hα (A + V)
    let J := pureFluxParity (Y := Y) (X := X)
    let eH := physicalConstantLoad Q e
    let f : pureFluxPair (Y := Y) (X := X) := pureFluxLoad eH
    let u := B f
    let s := (C * B * C) u
    responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) (k + H) -
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) k =
      (MeasureTheory.volume U).toReal⁻¹ *
        (-⟪J u, C u⟫_ℝ + ⟪J u, (C * B * C) u⟫_ℝ -
          ⟪J u, (C * B * C * B * C) u⟫_ℝ + ⟪J s, N s⟫_ℝ) := by
  let U := openCubeSet Q
  let α := ν / σ
  let hα : 0 < α := div_pos hν hσ
  let hU : MeasurableSet U := measurableSet_openCubeSet Q
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    dsimp [U]
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  let X := (physicalPotentialSpace Q).toSubmodule
  let Y := HilbertVectorL2 U
  let A : X →L[ℝ] Y := physicalProjectedCoefficient Q σ hσ k
  let V : X →L[ℝ] Y := physicalProjectedInsertion Q σ hσ H
  let C := pureFluxBlockOperator 0 V
  let B := pureFluxBlockInverse α hα A
  let N := pureFluxBlockInverse α hα (A + V)
  let J := pureFluxParity (Y := Y) (X := X)
  let eH := physicalConstantLoad Q e
  let f : pureFluxPair (Y := Y) (X := X) := pureFluxLoad eH
  let u := B f
  let s := (C * B * C) u
  have hCoefficient :
      physicalProjectedCoefficient Q σ hσ (k + H) = A + V := by
    simpa [A, V, physicalProjectedInsertion] using
      physicalProjectedCoefficient_add Q σ hσ k H
  have hOld := physical_response_eq_pureFlux_inverse Q ν σ hν hσ k e
  have hNew := physical_response_eq_pureFlux_inverse Q ν σ hν hσ (k + H) e
  have hOld' : responseFrameEnergyObservable hU hvol ν σ hν hσ (0, e) k =
      (MeasureTheory.volume U).toReal⁻¹ *
        pureFluxInverseQuadratic α hα A eH := by
    simpa [U, A, eH] using hOld
  have hNew' :
      responseFrameEnergyObservable hU hvol ν σ hν hσ (0, e) (k + H) =
        (MeasureTheory.volume U).toReal⁻¹ *
          pureFluxInverseQuadratic α hα (A + V) eH := by
    simpa [U, A, V, eH, hCoefficient] using hNew
  have hIdentity := pureFlux_block_resolvent_identity hα A V eH
  have hIdentity' :
      pureFluxInverseQuadratic α hα (A + V) eH -
        pureFluxInverseQuadratic α hα A eH =
        -⟪J u, C u⟫_ℝ + ⟪J u, (C * B * C) u⟫_ℝ -
          ⟪J u, (C * B * C * B * C) u⟫_ℝ + ⟪J s, N s⟫_ℝ := by
    simpa [C, B, N, J, f, u, s] using hIdentity
  change responseFrameEnergyObservable hU hvol ν σ hν hσ (0, e) (k + H) -
      responseFrameEnergyObservable hU hvol ν σ hν hσ (0, e) k = _
  calc
    responseFrameEnergyObservable hU hvol ν σ hν hσ (0, e) (k + H) -
        responseFrameEnergyObservable hU hvol ν σ hν hσ (0, e) k =
      (MeasureTheory.volume U).toReal⁻¹ *
          pureFluxInverseQuadratic α hα (A + V) eH -
        (MeasureTheory.volume U).toReal⁻¹ *
          pureFluxInverseQuadratic α hα A eH := by rw [hNew', hOld']
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          (pureFluxInverseQuadratic α hα (A + V) eH -
            pureFluxInverseQuadratic α hα A eH) := by ring
    _ = (MeasureTheory.volume U).toReal⁻¹ *
          (-⟪J u, C u⟫_ℝ + ⟪J u, (C * B * C) u⟫_ℝ -
            ⟪J u, (C * B * C * B * C) u⟫_ℝ + ⟪J s, N s⟫_ℝ) := by
      exact congrArg (fun z : ℝ => (MeasureTheory.volume U).toReal⁻¹ * z)
        hIdentity'

end

end ASDExplicitGamma.Scalar

end
