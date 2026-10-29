module

public import ASDExplicitGamma.Scalar.DropHessian

/-! Scaled four-term parity for SC-ONE-SHELL-RECIPROCAL-DROP: the response increment at
the insertion `(old, s • fresh)` has expectation `vol⁻¹ (s² E Hess + E Quartic_s)`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace Topology ENNReal

noncomputable section

theorem drop_physicalBlock_parityAdjoint {Y X : Type*}
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

theorem drop_newInverse_two_sided
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (x y : C(K, ℝ)) :
    (physicalParityOldBlock Q ν σ hσ R x +
      physicalParityInsertionBlock Q σ hσ R y) *
        physicalParityNewInverse Q ν σ hν hσ R x y = 1 ∧
    physicalParityNewInverse Q ν σ hν hσ R x y *
      (physicalParityOldBlock Q ν σ hσ R x +
        physicalParityInsertionBlock Q σ hσ R y) = 1 := by
  let A := physicalParityCoefficient Q σ hσ R
  let α := ν / σ
  have hα : 0 < α := div_pos hν hσ
  have hAdd : pureFluxBlockOperator α (A x) +
      pureFluxBlockOperator 0 (A y) =
        pureFluxBlockOperator α (A x + A y) :=
    pureFluxBlockOperator_add α (A x) (A y)
  constructor
  · change (pureFluxBlockOperator α (A x) +
      pureFluxBlockOperator 0 (A y)) *
        pureFluxBlockInverse α hα (A x + A y) = 1
    rw [hAdd]
    exact pureFluxBlockInverse_left α hα (A x + A y)
  · change pureFluxBlockInverse α hα (A x + A y) *
      (pureFluxBlockOperator α (A x) +
        pureFluxBlockOperator 0 (A y)) = 1
    rw [hAdd]
    exact pureFluxBlockInverse_right α hα (A x + A y)

theorem drop_scaled_parity {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (σ : ℝ) (hσ : 0 < σ) (e : Vec 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h) (s : ℝ) (hs : |s| ≤ 1) :
    ∫ p, physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ) e (p.1, s • p.2)
        ∂(physicalParityProductLaw M m) =
      (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        (s ^ 2 * (∫ p, physicalParityHessianObservable Q M.nu σ M.nu_pos hσ
              (physicalResponseRestriction Q hQ) e p
              ∂(physicalParityProductLaw M m)) +
          ∫ p, physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
              (physicalResponseRestriction Q hQ) e (p.1, s • p.2)
              ∂(physicalParityProductLaw M m)) := by
  let U := openCubeSet Q
  let R := physicalResponseRestriction Q hQ
  let ρ := (Cutoff.cutoffSampleLaw M).toMeasure
  let μold := physicalParityOldMarginal (K := K) M m
  let μfresh := physicalParityFreshMarginal (K := K) M m
  let A := physicalParityCoefficient Q σ hσ R
  let α := M.nu / σ
  let hα : 0 < α := div_pos M.nu_pos hσ
  let B := physicalParityOldInverse Q M.nu σ M.nu_pos hσ R
  let sc : C(K, ℝ) × C(K, ℝ) → C(K, ℝ) × C(K, ℝ) := fun p => (p.1, s • p.2)
  let C : C(K, ℝ) × C(K, ℝ) → physicalParityHilbert Q →L[ℝ] physicalParityHilbert Q :=
    fun p => physicalParityInsertionBlock Q σ hσ R (s • p.2)
  let N : C(K, ℝ) × C(K, ℝ) → physicalParityHilbert Q →L[ℝ] physicalParityHilbert Q :=
    fun p => pureFluxBlockInverse α hα (A p.1 + A (s • p.2))
  let J := pureFluxParity (Y := HilbertVectorL2 U)
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : pureFluxPair (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    pureFluxLoad (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  let hessian := physicalParityHessianObservable Q M.nu σ M.nu_pos hσ R e
  let quartic := physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ R e
  let linear := physicalParityLinearObservable Q M.nu σ M.nu_pos hσ R e
  let cubic := physicalParityCubicObservable Q M.nu σ M.nu_pos hσ R e
  have hX : Measurable (olderField K m) := measurable_olderField K ell m hK
  have hY : Measurable (physicalParityFreshField (K := K) m) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hJoint : ρ.map (fun ω => (olderField K m ω, physicalParityFreshField (K := K) m ω)) =
      μold.prod μfresh := by
    have hi := (indepFun_olderField_freshShell K M ell m hK).map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable
    exact hi
  letI : SFinite μold := by
    change SFinite (ρ.map (olderField K m))
    infer_instance
  letI : SFinite μfresh := by
    change SFinite (ρ.map (physicalParityFreshField (K := K) m))
    infer_instance
  let negFresh : C(K, ℝ) → C(K, ℝ) := fun y => -y
  have hnegFreshMeas : Measurable negFresh := by
    change Measurable (fun y : C(K, ℝ) => -y)
    fun_prop
  have hYlaw : μfresh =
      (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
        (shellFieldScalarRestriction K) := by
    calc
      μfresh = (ρ.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))).map
          (shellFieldScalarRestriction K) := by
            dsimp [μfresh, physicalParityFreshMarginal, physicalParityFreshField]
            rw [Measure.map_map (measurable_shellFieldScalarRestriction K)
              ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)]
            rfl
      _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (shellFieldScalarRestriction K) := by
            rw [← Model.map_freshShell_eq_shellMarginalLaw M m]
  have hnegShell : Measure.map (ShellField.negate (d := 2))
      (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure =
        (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure :=
    Algsuperdiff.Section3.Provider.Corrector.map_negate_shellMarginalLaw M (m + 1)
  have hneg : Measure.map negFresh μfresh = μfresh := by
    rw [hYlaw]
    calc
      Measure.map negFresh
          ((ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
            (shellFieldScalarRestriction K)) =
        (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (fun j => -shellFieldScalarRestriction K j) := by
            rw [Measure.map_map hnegFreshMeas
              (measurable_shellFieldScalarRestriction K)]
            rfl
      _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (fun j => shellFieldScalarRestriction K (ShellField.negate j)) := by
            congr 1
            funext j
            exact (shellFieldScalarRestriction_negate K j).symm
      _ = ((ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (ShellField.negate (d := 2))).map
            (shellFieldScalarRestriction K) := by
              exact (Measure.map_map (measurable_shellFieldScalarRestriction K)
                ShellField.measurable_negate).symm
      _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (shellFieldScalarRestriction K) := by
        rw [hnegShell]
  have hflip : Measure.map (fun p : C(K, ℝ) × C(K, ℝ) => (p.1, negFresh p.2))
      (μold.prod μfresh) = μold.prod μfresh :=
    product_fresh_flip_preserves μold μfresh negFresh hnegFreshMeas hneg
  let negPair : C(K, ℝ) × C(K, ℝ) → C(K, ℝ) × C(K, ℝ) :=
    fun p => (p.1, negFresh p.2)
  obtain ⟨c, hc0, hcs⟩ := drop_scaled_terms Q hQ M m σ hσ e h hM
  obtain ⟨hlinearInt, hhessianInt, hcubicInt, hquarticInt, -⟩ := hcs s hs
  have hnegPairMeas : Measurable negPair := by
    change Measurable (fun p : C(K, ℝ) × C(K, ℝ) => (p.1, -p.2))
    fun_prop
  have hMparity (p : C(K, ℝ) × C(K, ℝ)) :
      (physicalParityOldBlock Q M.nu σ hσ R p.1).adjoint * J =
        J * physicalParityOldBlock Q M.nu σ hσ R p.1 :=
    drop_physicalBlock_parityAdjoint α (A p.1)
  have hCparity (p : C(K, ℝ) × C(K, ℝ)) :
      (C p).adjoint * J = J * C p :=
    drop_physicalBlock_parityAdjoint 0 (A (s • p.2))
  have hBM (p : C(K, ℝ) × C(K, ℝ)) :
      B p.1 * physicalParityOldBlock Q M.nu σ hσ R p.1 = 1 :=
    pureFluxBlockInverse_right α hα (A p.1)
  have hMB (p : C(K, ℝ) × C(K, ℝ)) :
      physicalParityOldBlock Q M.nu σ hσ R p.1 * B p.1 = 1 :=
    pureFluxBlockInverse_left α hα (A p.1)
  have hMN (p : C(K, ℝ) × C(K, ℝ)) :
      (physicalParityOldBlock Q M.nu σ hσ R p.1 + C p) * N p = 1 :=
    (drop_newInverse_two_sided Q M.nu σ M.nu_pos hσ R p.1 (s • p.2)).1
  have hNM (p : C(K, ℝ) × C(K, ℝ)) :
      N p * (physicalParityOldBlock Q M.nu σ hσ R p.1 + C p) = 1 :=
    (drop_newInverse_two_sided Q M.nu σ M.nu_pos hσ R p.1 (s • p.2)).2
  have hBneg (p : C(K, ℝ) × C(K, ℝ)) : B (negPair p).1 = B p.1 := rfl
  have hCneg (p : C(K, ℝ) × C(K, ℝ)) : C (negPair p) = -(C p) := by
    change physicalParityInsertionBlock Q σ hσ R (s • -p.2) =
      -physicalParityInsertionBlock Q σ hσ R (s • p.2)
    rw [smul_neg]
    exact physicalParity_insertion_neg' Q σ hσ R (s • p.2)
  have hf : J f = f := by simp [J, f, pureFluxParity, pureFluxLoad]
  have hparity := resolvent_hilbert_parity_random_old
    (μold.prod μfresh) negPair hnegPairMeas hflip
    (fun p => physicalParityOldBlock Q M.nu σ hσ R p.1)
    (fun p => B p.1) J hMparity hBM hMB
    C N hCparity hMN hNM hBneg hCneg f hf
    hlinearInt hhessianInt hcubicInt hquarticInt
  let volInv := (MeasureTheory.volume U).toReal⁻¹
  let qdiff : C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
    ⟪f, N p f⟫_ℝ - ⟪f, B p.1 f⟫_ℝ
  have hquadPoint (p : C(K, ℝ) × C(K, ℝ)) :
      qdiff p = linear (sc p) + hessian (sc p) + cubic (sc p) + quartic (sc p) := by
    have h := resolvent_four_term_hilbert_pairing
      (physicalParityOldBlock Q M.nu σ hσ R p.1) (C p) (B p.1)
      (N p) J (hMparity p) (hCparity p) (hBM p) (hMB p)
      (hMN p) (hNM p) f hf
    exact h
  have hresponsePoint (p : C(K, ℝ) × C(K, ℝ)) :
      physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ R e (sc p) =
        volInv * qdiff p := by
    rw [physicalParity_response_pointwise' Q M.nu σ M.nu_pos hσ R e p.1 (s • p.2)]
    congr 1
    exact (hquadPoint p).symm
  have hqdInt : Integrable qdiff (μold.prod μfresh) := by
    have hi := (hlinearInt.add hhessianInt).add (hcubicInt.add hquarticInt)
    refine hi.congr ?_
    filter_upwards with p
    simp only [Pi.add_apply]
    rw [hquadPoint p]
    ring
  have hparityLast :
      (∫ p, qdiff p ∂(μold.prod μfresh)) =
        (∫ p, hessian (sc p) ∂(μold.prod μfresh)) +
          (∫ p, quartic (sc p) ∂(μold.prod μfresh)) := by
    exact hparity.2.2
  have hH : (∫ p, hessian (sc p) ∂(μold.prod μfresh)) =
      s ^ 2 * ∫ p, hessian p ∂(μold.prod μfresh) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun p => drop_hessian_smul Q M.nu σ M.nu_pos hσ R e s p.1 p.2))
  change ∫ p, physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ R e (sc p)
      ∂(μold.prod μfresh) = volInv * (s ^ 2 * (∫ p, hessian p ∂(μold.prod μfresh)) +
        ∫ p, quartic (sc p) ∂(μold.prod μfresh))
  calc (∫ p, physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ R e (sc p)
        ∂(μold.prod μfresh)) = ∫ p, volInv * qdiff p ∂(μold.prod μfresh) :=
        integral_congr_ae (Filter.Eventually.of_forall hresponsePoint)
    _ = volInv * ∫ p, qdiff p ∂(μold.prod μfresh) := by rw [integral_const_mul]
    _ = _ := by rw [hparityLast, hH]

end

end ASDExplicitGamma.Scalar
