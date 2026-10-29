module

public import ASDExplicitGamma.Response.CoefficientFamily
public import ASDExplicitGamma.Response.EnergyHilbert
public import ASDExplicitGamma.Response.LinearShear

@[expose] public section

namespace ASDExplicitGamma.Response

open Homogenization

noncomputable section

/-- The coefficient field `ν I + k J` associated to a bounded continuous
skew amplitude on the closed response domain. -/
def responsePlanarCoefficientField {U : Set (Vec 2)} (ν : ℝ)
    (k : ResponseCoefficient U) : CoeffField 2 :=
  fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x)

theorem responsePlanarCoefficientField_isElliptic {U : Set (Vec 2)}
    (hU : MeasurableSet U) (ν : ℝ) (hν : 0 < ν)
    (k : ResponseCoefficient U) :
    IsEllipticFieldOn ν ((ν ^ 2 + ‖k‖ ^ 2) / ν) U
      (responsePlanarCoefficientField ν k) := by
  let a := responsePlanarCoefficientField ν k
  have ha : ∀ i j, Continuous (fun x => a x i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, responsePlanarCoefficientField, responsePlanarCoefficient,
        responsePlanarJ] <;> fun_prop
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    exact Measurable.ite hU (ha i j).measurable measurable_const
  · intro x hx
    have hkx : |responseCoefficientExtension k x| ≤ ‖k‖ := by
      calc
        |responseCoefficientExtension k x| =
            ‖responseCoefficientExtension k x‖ := by simp
        _ ≤ ‖responseCoefficientExtension k‖ :=
            (responseCoefficientExtension k).norm_coe_le_norm x
        _ = ‖k‖ := responseCoefficientExtension_norm k
    exact responsePlanarCoefficient_isElliptic ν ‖k‖
      (responseCoefficientExtension k x) hν hkx

/-- The coefficient in the fixed frame is the original planar coefficient
scaled by `σ⁻¹`; this is the coefficient whose doubled energy is the frame
energy. -/
def responseFramePlanarCoefficientField {U : Set (Vec 2)}
    (ν σ : ℝ) (k : ResponseCoefficient U) : CoeffField 2 :=
  fun x => responsePlanarCoefficient (ν / σ)
    (responseCoefficientExtension k x / σ)

theorem responseFramePlanarCoefficientField_apply {U : Set (Vec 2)}
    (ν σ : ℝ) (k : ResponseCoefficient U) (x : Vec 2) :
    responseFramePlanarCoefficientField ν σ k x =
      responsePlanarCoefficient (ν / σ) (responseCoefficientExtension k x / σ) := rfl

theorem responseFramePlanarCoefficientField_isElliptic {U : Set (Vec 2)}
    (hU : MeasurableSet U) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) :
    IsEllipticFieldOn (ν / σ)
      (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U
      (responseFramePlanarCoefficientField ν σ k) := by
  let a := responseFramePlanarCoefficientField ν σ k
  have ha : ∀ i j, Continuous (fun x => a x i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [a, responseFramePlanarCoefficientField, responsePlanarCoefficient,
        responsePlanarJ] <;> fun_prop
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    exact Measurable.ite hU (ha i j).measurable measurable_const
  · intro x hx
    have hkx : |responseCoefficientExtension k x / σ| ≤ ‖k‖ / σ := by
      rw [abs_div, abs_of_pos hσ]
      apply div_le_div_of_nonneg_right ?_ hσ.le
      calc
        |responseCoefficientExtension k x| =
            ‖responseCoefficientExtension k x‖ := by simp
        _ ≤ ‖responseCoefficientExtension k‖ :=
            (responseCoefficientExtension k).norm_coe_le_norm x
        _ = ‖k‖ := responseCoefficientExtension_norm k
    exact responsePlanarCoefficient_isElliptic (ν / σ) (‖k‖ / σ)
      (responseCoefficientExtension k x / σ) (div_pos hν hσ) hkx

/-- The fixed-frame Coarse operator system; its coefficient is
`(ν I + k J) / σ`, so its energy is independent of future perturbations. -/
noncomputable def responseFrameMuOperatorSystemData {U : Set (Vec 2)}
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) :
    MuOperatorSystemData U (responseFramePlanarCoefficientField ν σ k) :=
  (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuOperatorSystemDataOfIsEllipticFieldOn
    (responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k) hvol

/-- The deterministic system's Hilbert energy is the average of its pointwise
block quadratic form, expressed on the canonical `L²` representative. -/
theorem muSystem_energy_eq_volumeAverage {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField 2}
    (M : MuOperatorSystemData U a) (X : HilbertBlockL2 U) :
    (M.toMuHilbertRealization).energyBilin X X =
      volumeAverage U (fun x =>
        blockVecDot (hilbertBlockL2ToBlockL2 X x)
          (blockMatVecMul (blockCoeffField a x)
            (hilbertBlockL2ToBlockL2 X x))) := by
  let F : BlockL2 U := hilbertBlockL2ToBlockL2 X
  have hF : MemBlockL2 U (fun x => F x) := F.property
  have hX : toHilbertBlockL2OfBlockField hF = X := by
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField hF,
      coeFn_hilbertBlockL2ToBlockL2 X] with x hfield htransport
    calc
      (toHilbertBlockL2OfBlockField hF) x =
          hilbertifyBlockField (fun x => F x) x := hfield
      _ = HilbertBlockVec.ofBlockVec ((hilbertBlockL2ToBlockL2 X x)) := by
        simp [hilbertifyBlockField, F]
      _ = X x := by
        rw [htransport]
        simp
  calc
    (M.toMuHilbertRealization).energyBilin X X =
        energyBilinOfOperator M.toMuOperatorRealization.operator X X := rfl
    _ = energyBilinOfOperator M.toMuOperatorRealization.operator
          (toHilbertBlockL2OfBlockField hF)
          (toHilbertBlockL2OfBlockField hF) := by rw [hX]
    _ = volumeAverage U (fun x =>
          blockVecDot (F x) (blockMatVecMul (blockCoeffField a x) (F x))) :=
        M.toMuOperatorRealization.energyBilin_eq_volumeAverage_swap_of_memBlockL2
          hF hF
    _ = volumeAverage U (fun x =>
          blockVecDot (hilbertBlockL2ToBlockL2 X x)
            (blockMatVecMul (blockCoeffField a x)
              (hilbertBlockL2ToBlockL2 X x))) := by rfl

/-- For the fixed-frame coefficient `(ν I + k J)/σ`, the Coarse Hilbert
energy is exactly the average of the frame energy density. -/
theorem responseFrameMu_energy_eq_volumeAverage_density {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U)
    (X : HilbertBlockL2 U) :
    (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin
        X X =
      volumeAverage U (fun x => responseFrameEnergyDensity ν σ
        (responseCoefficientExtension k x) (hilbertBlockL2ToBlockL2 X x)) := by
  rw [muSystem_energy_eq_volumeAverage]
  unfold volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
  simpa [responseFramePlanarCoefficientField, blockCoeffField] using
    (responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ
      (responseCoefficientExtension k x) hν hσ
      (hilbertBlockL2ToBlockL2 X x)).symm

/-- The Coarse minimizer's coercive energy form, installed as the Hilbert
inner product on the fixed coefficient's `L²` carrier. -/
noncomputable def responseEnergyHilbertData {U : Set (Vec 2)}
    {a : CoeffField 2} (M : MuHilbertRealization U a) :
    EnergyHilbertData (H := HilbertBlockL2 U) where
  energy := M.energyBilin
  symmetric := M.energySymm
  coercive := M.energyCoercive

private theorem responseShearPointwise_toBlockVec (σ η : ℝ)
    (X : HilbertBlockVec 2) :
    (η • responseShearPointwiseOperator σ 1 X).toBlockVec =
      responseShearCorrection σ η X.toBlockVec := by
  rw [responseShearPointwiseOperator_apply]
  apply Prod.ext
  · ext i
    simp [HilbertVec.toVec, responseShearCorrection]
  · ext i
    simp [HilbertVec.toVec, responseShearCorrection,
      div_eq_mul_inv, smul_smul]

/-- On the plain block representative, the L² shear acts by the pointwise
correction formula almost everywhere. -/
theorem responseShearL2Operator_toBlockL2_ae {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) =ᵐ[volumeMeasureOn U]
      fun x => responseShearCorrection σ (responseCoefficientExtension H x)
        (hilbertBlockL2ToBlockL2 X x) := by
  filter_upwards [coeFn_hilbertBlockL2ToBlockL2
      (responseShearL2Operator σ hσ H X),
    (responseShearOperatorField σ hσ H).coeFn_toContinuousLinearMap X,
    coeFn_hilbertBlockL2ToBlockL2 X] with x houtput hoperator hinput
  rw [houtput]
  change ((responseShearOperatorField σ hσ H).toContinuousLinearMap X x).toBlockVec = _
  rw [hoperator, hinput]
  change (responseCoefficientExtension H x • responseShearPointwiseOperator σ 1
      (X x)).toBlockVec = _
  exact responseShearPointwise_toBlockVec σ (responseCoefficientExtension H x) (X x)

/-- The affine change of variables `I + C_H` is the pointwise shear on
the plain block representative. -/
theorem responseShearAffineL2_toBlockL2_ae {U : Set (Vec 2)}
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    hilbertBlockL2ToBlockL2 (X + responseShearL2Operator σ hσ H X) =ᵐ[volumeMeasureOn U]
      fun x => responseShear σ (responseCoefficientExtension H x)
        (hilbertBlockL2ToBlockL2 X x) := by
  have hmap : hilbertBlockL2ToBlockL2
      (X + responseShearL2Operator σ hσ H X) =
      hilbertBlockL2ToBlockL2 X +
        hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) := by
    exact map_add (hilbertBlockL2ToBlockL2 (U := U)) X _
  rw [hmap]
  filter_upwards [MeasureTheory.Lp.coeFn_add
      (hilbertBlockL2ToBlockL2 X)
      (hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X)),
    responseShearL2Operator_toBlockL2_ae σ hσ H X] with x hadd hshear
  calc
    (hilbertBlockL2ToBlockL2 X +
        hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X)) x =
      hilbertBlockL2ToBlockL2 X x +
        hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) x := hadd
    _ = hilbertBlockL2ToBlockL2 X x +
        responseShearCorrection σ (responseCoefficientExtension H x)
          (hilbertBlockL2ToBlockL2 X x) := by rw [hshear]
    _ = responseShear σ (responseCoefficientExtension H x)
          (hilbertBlockL2ToBlockL2 X x) := rfl

/-- Perturbing the frame coefficient is exactly the fixed-base energy of the
affine shear, before taking the minimum. -/
theorem responseFrameMu_energy_shear_identity {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin
        (X + responseShearL2Operator σ hσ H X)
        (X + responseShearL2Operator σ hσ H X) =
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + H)).toMuHilbertRealization.energyBilin
        X X := by
  rw [responseFrameMu_energy_eq_volumeAverage_density hU hvol ν σ hν hσ k _,
    responseFrameMu_energy_eq_volumeAverage_density hU hvol ν σ hν hσ (k + H) X]
  unfold volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hU,
    responseShearAffineL2_toBlockL2_ae σ hσ H X] with x hx hshear
  rw [hshear, responseCoefficientExtension_add_on k H hx]
  exact (responseFrameEnergyDensity_shear ν σ
    (responseCoefficientExtension k x) (responseCoefficientExtension H x)
    (hilbertBlockL2ToBlockL2 X x)).symm

private theorem responseFrameDensity_integrable {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (F : BlockL2 U) :
    MeasureTheory.IntegrableOn (fun x => responseFrameEnergyDensity ν σ
      (responseCoefficientExtension k x) (F x)) U := by
  let Xstate : BlockState 2 :=
    ⟨fun x => (F x).1, fun x => (F x).2⟩
  have hF : MemBlockL2 U Xstate.eval := by
    have hEq : (fun x => F x) =ᵐ[volumeMeasureOn U] Xstate.eval := by
      filter_upwards [] with x
      simp [Xstate, BlockState.eval]
    exact (MeasureTheory.memLp_congr_ae hEq).1 (MeasureTheory.Lp.memLp F)
  have hpair :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hF hF (responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k)
  have hEq : (fun x => responseFrameEnergyDensity ν σ
      (responseCoefficientExtension k x) (F x)) =
      blockPairingIntegrand (responseFramePlanarCoefficientField ν σ k)
        Xstate Xstate := by
    funext x
    simpa [Xstate, BlockState.eval, blockPairingIntegrand,
      responseFramePlanarCoefficientField, blockCoeffField] using
      responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ
        (responseCoefficientExtension k x) hν hσ (F x)
  exact hpair.congr (Filter.Eventually.of_forall fun x => congrFun hEq.symm x)

private theorem responseCoefficientExtension_abs_apply_le {U : Set (Vec 2)}
    (H : ResponseCoefficient U) (x : Vec 2) :
    |responseCoefficientExtension H x| ≤ ‖H‖ := by
  calc
    |responseCoefficientExtension H x| =
        ‖responseCoefficientExtension H x‖ := by simp
    _ ≤ ‖responseCoefficientExtension H‖ :=
      (responseCoefficientExtension H).norm_coe_le_norm x
    _ = ‖H‖ := responseCoefficientExtension_norm H

private theorem responseFrameEnergyDensity_shearCorrection_le_norm
    (ν σ κ η M : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (hη : |η| ≤ M) (X : BlockVec 2) :
    responseFrameEnergyDensity ν σ κ (responseShearCorrection σ η X) ≤
      (M / ν) ^ 2 * responseFrameEnergyDensity ν σ κ X := by
  have hratio : |η| / ν ≤ M / ν := div_le_div_of_nonneg_right hη hν.le
  have hratioSq : (|η| / ν) ^ 2 ≤ (M / ν) ^ 2 :=
    (sq_le_sq₀ (div_nonneg (abs_nonneg η) hν.le)
      (div_nonneg (le_trans (abs_nonneg η) hη) hν.le)).2 hratio
  have hbase : 0 ≤ responseFrameEnergyDensity ν σ κ X := by
    simp only [responseFrameEnergyDensity]
    exact add_nonneg
      (mul_nonneg (div_nonneg hν.le hσ.le) (vecNormSq_nonneg X.1))
      (mul_nonneg (div_nonneg hσ.le hν.le)
        (vecNormSq_nonneg (X.2 - (κ / σ) • matVecMul responsePlanarJ X.1)))
  calc
    responseFrameEnergyDensity ν σ κ (responseShearCorrection σ η X) ≤
        (|η| / ν) ^ 2 * responseFrameEnergyDensity ν σ κ X :=
      responseFrameEnergyDensity_shearCorrection_le ν σ κ η hν hσ X
    _ ≤ (M / ν) ^ 2 * responseFrameEnergyDensity ν σ κ X :=
      mul_le_mul_of_nonneg_right hratioSq hbase

theorem responseFrameMu_shearOperator_energy_bound {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin
        (responseShearL2Operator σ hσ H X)
        (responseShearL2Operator σ hσ H X) ≤
      (‖H‖ / ν) ^ 2 *
        (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin
          X X := by
  let f : Vec 2 → ℝ := fun x => responseFrameEnergyDensity ν σ
    (responseCoefficientExtension k x)
    (hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X) x)
  let g : Vec 2 → ℝ := fun x => responseFrameEnergyDensity ν σ
    (responseCoefficientExtension k x) (hilbertBlockL2ToBlockL2 X x)
  let c : ℝ := (‖H‖ / ν) ^ 2
  have hIf : MeasureTheory.IntegrableOn f U := by
    simpa [f] using responseFrameDensity_integrable hU ν σ hν hσ k
      (hilbertBlockL2ToBlockL2 (responseShearL2Operator σ hσ H X))
  have hIg : MeasureTheory.IntegrableOn g U := by
    simpa [g] using responseFrameDensity_integrable hU ν σ hν hσ k
      (hilbertBlockL2ToBlockL2 X)
  have hIc : MeasureTheory.IntegrableOn (fun x => c * g x) U := by
    change MeasureTheory.Integrable (fun x => c * g x)
      (MeasureTheory.volume.restrict U)
    have hEq : (fun x => c * g x) = c • g := by
      funext x
      simp [smul_eq_mul]
    rw [hEq]
    exact hIg.smul c
  have hPointwise : ∀ᵐ x ∂volumeMeasureOn U, f x ≤ c * g x := by
    filter_upwards [responseShearL2Operator_toBlockL2_ae σ hσ H X] with x hshear
    have hη := responseCoefficientExtension_abs_apply_le H x
    have hbound := responseFrameEnergyDensity_shearCorrection_le_norm
      ν σ (responseCoefficientExtension k x) (responseCoefficientExtension H x)
      ‖H‖ hν hσ hη (hilbertBlockL2ToBlockL2 X x)
    simpa [f, g, c, hshear] using hbound
  have hIntegral : (∫ x in U, f x ∂MeasureTheory.volume) ≤
      ∫ x in U, c * g x ∂MeasureTheory.volume := by
    exact MeasureTheory.integral_mono_ae hIf hIc hPointwise
  rw [responseFrameMu_energy_eq_volumeAverage_density hU hvol ν σ hν hσ k
      (responseShearL2Operator σ hσ H X),
    responseFrameMu_energy_eq_volumeAverage_density hU hvol ν σ hν hσ k X]
  change volumeAverage U f ≤ c * volumeAverage U g
  unfold volumeAverage c
  calc
    (MeasureTheory.volume U).toReal⁻¹ *
        ∫ x in U, f x ∂MeasureTheory.volume ≤
      (MeasureTheory.volume U).toReal⁻¹ *
        ∫ x in U, (‖H‖ / ν) ^ 2 * g x ∂MeasureTheory.volume :=
      mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = (‖H‖ / ν) ^ 2 *
        ((MeasureTheory.volume U).toReal⁻¹ *
          ∫ x in U, g x ∂MeasureTheory.volume) := by
      rw [MeasureTheory.integral_const_mul]
      ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def responseEnergyDownLinear (D : EnergyHilbertData (H := H)) :
    EnergyCarrier D →ₗ[ℝ] H where
  toFun := ULift.down
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def responseEnergyUp (D : EnergyHilbertData (H := H)) (x : H) : EnergyCarrier D :=
  ULift.up x

omit [CompleteSpace H] in
@[simp] theorem responseEnergyUp_down (D : EnergyHilbertData (H := H)) (x : H) :
    (responseEnergyUp D x).down = x := rfl

def responseEnergyUpLinear (D : EnergyHilbertData (H := H)) :
    H →ₗ[ℝ] EnergyCarrier D where
  toFun := responseEnergyUp D
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

omit [CompleteSpace H] in
private theorem responseEnergyDown_norm_le (D : EnergyHilbertData (H := H))
    (x : EnergyCarrier D) :
    ‖x.down‖ ≤ (Real.sqrt D.coercive.choose)⁻¹ * ‖x‖ := by
  have hc : 0 < Real.sqrt D.coercive.choose := Real.sqrt_pos.2 D.coercive.choose_spec.1
  have hlow := energyCarrier_norm_lower D x
  have hdiv := div_le_div_of_nonneg_right hlow hc.le
  have hcancel :
      (Real.sqrt D.coercive.choose * ‖x.down‖) /
        Real.sqrt D.coercive.choose = ‖x.down‖ := by
    let a := Real.sqrt D.coercive.choose
    let b := ‖x.down‖
    calc
      (Real.sqrt D.coercive.choose * ‖x.down‖) /
          Real.sqrt D.coercive.choose = b * (a / a) := by
        dsimp [a, b]
        rw [mul_comm, mul_div_assoc]
      _ = ‖x.down‖ := by
        dsimp [a, b]
        rw [div_self hc.ne', mul_one]
  calc
    ‖x.down‖ =
        (Real.sqrt D.coercive.choose * ‖x.down‖) /
          Real.sqrt D.coercive.choose := hcancel.symm
    _ ≤ ‖x‖ / Real.sqrt D.coercive.choose := hdiv
    _ = (Real.sqrt D.coercive.choose)⁻¹ * ‖x‖ := by ring

omit [CompleteSpace H] in
private theorem responseEnergyUp_norm_le (D : EnergyHilbertData (H := H))
    (x : H) :
    ‖responseEnergyUp D x‖ ≤
      Real.sqrt (‖D.energy‖ + 1) * ‖x‖ := by
  calc
    ‖responseEnergyUp D x‖ ≤
        Real.sqrt (‖D.energy‖ + 1) * ‖(responseEnergyUp D x).down‖ :=
      energyCarrier_norm_le D (responseEnergyUp D x)
    _ = Real.sqrt (‖D.energy‖ + 1) * ‖x‖ := by rfl

noncomputable def responseEnergyDownCLM (D : EnergyHilbertData (H := H)) :
    EnergyCarrier D →L[ℝ] H :=
  (responseEnergyDownLinear D).mkContinuous
    (Real.sqrt D.coercive.choose)⁻¹ (by
      intro x
      change ‖x.down‖ ≤ (Real.sqrt D.coercive.choose)⁻¹ * ‖x‖
      exact responseEnergyDown_norm_le D x)

noncomputable def responseEnergyUpCLM (D : EnergyHilbertData (H := H)) :
    H →L[ℝ] EnergyCarrier D :=
  (responseEnergyUpLinear D).mkContinuous
    (Real.sqrt (‖D.energy‖ + 1)) (by
      intro x
      exact responseEnergyUp_norm_le D x)

noncomputable def responseEnergyUpCLMNorm
    (D : EnergyHilbertData (H := H)) : ℝ :=
  ‖(responseEnergyUpCLM (H := H) D :
    H →L[ℝ] EnergyCarrier (H := H) D)‖

noncomputable def responseEnergyDownCLMNorm
    (D : EnergyHilbertData (H := H)) : ℝ :=
  ‖(responseEnergyDownCLM (H := H) D :
    EnergyCarrier (H := H) D →L[ℝ] H)‖

omit [CompleteSpace H] in
@[simp] theorem responseEnergyDownCLM_apply (D : EnergyHilbertData (H := H))
    (x : EnergyCarrier D) : responseEnergyDownCLM D x = x.down := by
  change (responseEnergyDownLinear D).mkContinuous _ _ x = x.down
  rw [LinearMap.mkContinuous_apply]
  rfl

/-- The Coarse correction space transported to the equivalent energy Hilbert
carrier. -/
def responseEnergyCorrectionSpace {U : Set (Vec 2)} {a : CoeffField 2}
    (M : MuHilbertRealization U a)
    (D : EnergyHilbertData (H := HilbertBlockL2 U)) :
    ClosedSubmodule ℝ (EnergyCarrier D) :=
  M.correctionSpace.correctionSpace.comap (responseEnergyDownCLM D)

@[simp] theorem responseEnergyCorrectionSpace_mem_iff {U : Set (Vec 2)}
    {a : CoeffField 2} (M : MuHilbertRealization U a)
    (D : EnergyHilbertData (H := HilbertBlockL2 U)) (z : EnergyCarrier D) :
    z ∈ responseEnergyCorrectionSpace M D ↔
      z.down ∈ M.correctionSpace.correctionSpace := Iff.rfl

omit [CompleteSpace H] in
@[simp] theorem responseEnergyUpCLM_apply (D : EnergyHilbertData (H := H))
    (x : H) : responseEnergyUpCLM D x = responseEnergyUp D x := by
  change (responseEnergyUpLinear D).mkContinuous _ _ x = responseEnergyUp D x
  rw [LinearMap.mkContinuous_apply]
  rfl

/-- The Coarse minimizer is orthogonal to the transported correction space in
the energy Hilbert norm. -/
theorem responseEnergyMinimizer_orthogonal {U : Set (Vec 2)}
    {a : CoeffField 2} (M : MuHilbertRealization U a) (P : BlockVec 2)
    (Y : (responseEnergyCorrectionSpace M (responseEnergyHilbertData M)).toSubmodule) :
    inner ℝ (responseEnergyUp (responseEnergyHilbertData M) (M.minimizerMap P)) Y = 0 := by
  change M.energyBilin (M.minimizerMap P)
    (Y : EnergyCarrier (responseEnergyHilbertData M)).down = 0
  exact M.minimizerMap_firstVariation P
    ⟨(Y : EnergyCarrier (responseEnergyHilbertData M)).down,
      (responseEnergyCorrectionSpace_mem_iff M
        (responseEnergyHilbertData M) Y).mp Y.property⟩

/-- Conjugate a standard-carrier operator into the fixed energy Hilbert
carrier. -/
noncomputable def responseEnergyConjugateOperator
    (D : EnergyHilbertData (H := H)) :
    (H →L[ℝ] H) →ₗ[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) where
  toFun A := (responseEnergyUpCLM (H := H) D).comp
    (A.comp (responseEnergyDownCLM (H := H) D))
  map_add' := by
    intro A B
    apply ContinuousLinearMap.ext
    intro x
    simp [ContinuousLinearMap.comp_apply]
  map_smul' := by
    intro c A
    apply ContinuousLinearMap.ext
    intro x
    simp [ContinuousLinearMap.comp_apply]

omit [CompleteSpace H] in
@[simp] theorem responseEnergyConjugateOperator_apply
    (D : EnergyHilbertData (H := H)) (A : H →L[ℝ] H)
    (x : EnergyCarrier D) :
    responseEnergyConjugateOperator D A x = ULift.up (A x.down) := by
  change responseEnergyUpCLM D (A (responseEnergyDownCLM D x)) =
    responseEnergyUp D (A x.down)
  rw [responseEnergyUpCLM_apply, responseEnergyDownCLM_apply]

omit [CompleteSpace H] in
theorem responseEnergyConjugateOperator_pairwise_nilpotent
    (D : EnergyHilbertData (H := H)) (A B : H →L[ℝ] H)
    (hAB : A ∘L B = 0) :
    responseEnergyConjugateOperator D A ∘L
      responseEnergyConjugateOperator D B = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change responseEnergyConjugateOperator D A
    (responseEnergyConjugateOperator D B x) = 0
  rw [responseEnergyConjugateOperator_apply,
    responseEnergyConjugateOperator_apply]
  have hzero : A (B x.down) = 0 := by
    have h := congrArg (fun T : H →L[ℝ] H => T x.down) hAB
    simpa [ContinuousLinearMap.comp_apply] using h
  rw [hzero]
  change responseEnergyUp D (0 : H) = 0
  rfl

/-- The coefficient-indexed family of nilpotent shears, represented on the
fixed Coarse energy Hilbert space at base coefficient `k`. -/
noncomputable def responseEnergyShearFamilyLinear {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ)
    (D : EnergyHilbertData (H := HilbertBlockL2 U)) :
    ResponseCoefficient U →ₗ[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) where
  toFun H := responseEnergyConjugateOperator D
    (responseShearL2Operator σ hσ H)
  map_add' := by
    intro H K
    apply ContinuousLinearMap.ext
    intro x
    simp [responseEnergyConjugateOperator, ContinuousLinearMap.comp_apply,
      responseShearL2Operator_add hU σ hσ]
  map_smul' := by
    intro c H
    apply ContinuousLinearMap.ext
    intro x
    simp [responseEnergyConjugateOperator, ContinuousLinearMap.comp_apply,
      responseShearL2Operator_smul hU σ hσ]

theorem responseEnergyShearFamilyLinear_pairwise_nilpotent {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (H K : ResponseCoefficient U) :
    responseEnergyShearFamilyLinear hU σ hσ D H ∘L
      responseEnergyShearFamilyLinear hU σ hσ D K = 0 := by
  apply responseEnergyConjugateOperator_pairwise_nilpotent
  exact responseShearL2Operator_pairwise_nilpotent σ hσ H K

omit [CompleteSpace H] in
theorem responseEnergyConjugateOperator_norm_le
    (D : EnergyHilbertData (H := H)) (A : H →L[ℝ] H) :
    ‖responseEnergyConjugateOperator D A‖ ≤
      (responseEnergyUpCLMNorm (H := H) D *
        responseEnergyDownCLMNorm (H := H) D) * ‖A‖ := by
  let cup : ℝ := responseEnergyUpCLMNorm (H := H) D
  let cdown : ℝ := responseEnergyDownCLMNorm (H := H) D
  calc
    ‖responseEnergyConjugateOperator D A‖ ≤
        cup *
          ‖A.comp (responseEnergyDownCLM (H := H) D)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ cup * (‖A‖ * cdown) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg (responseEnergyUpCLM (H := H) D))
        change ‖A.comp (responseEnergyDownCLM (H := H) D)‖ ≤
          ‖A‖ * responseEnergyDownCLMNorm D
        simpa [responseEnergyDownCLMNorm] using
          ContinuousLinearMap.opNorm_comp_le A (responseEnergyDownCLM (H := H) D)
    _ = (cup * cdown) * ‖A‖ := by ring
    _ = (responseEnergyUpCLMNorm D * responseEnergyDownCLMNorm D) * ‖A‖ := rfl

theorem responseEnergyShearFamilyLinear_norm_le {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (H : ResponseCoefficient U) :
    ‖responseEnergyShearFamilyLinear hU σ hσ D H‖ ≤
      (responseEnergyUpCLMNorm (H := HilbertBlockL2 U) D *
        responseEnergyDownCLMNorm (H := HilbertBlockL2 U) D) * (‖H‖ / σ) := by
  have hL2 : ‖responseShearL2Operator σ hσ H‖ ≤ ‖H‖ / σ :=
    responseShearL2Operator_opNorm_le σ hσ H
  have hC : 0 ≤ responseEnergyUpCLMNorm D * responseEnergyDownCLMNorm D := by
    change 0 ≤ ‖responseEnergyUpCLM (H := HilbertBlockL2 U) D‖ *
      ‖responseEnergyDownCLM (H := HilbertBlockL2 U) D‖
    positivity
  calc
    ‖responseEnergyShearFamilyLinear hU σ hσ D H‖ =
        ‖responseEnergyConjugateOperator D
          (responseShearL2Operator σ hσ H)‖ := rfl
    _ ≤ (responseEnergyUpCLMNorm (H := HilbertBlockL2 U) D *
        responseEnergyDownCLMNorm (H := HilbertBlockL2 U) D) *
        ‖responseShearL2Operator σ hσ H‖ :=
          responseEnergyConjugateOperator_norm_le D _
    _ ≤ (responseEnergyUpCLMNorm (H := HilbertBlockL2 U) D *
        responseEnergyDownCLMNorm (H := HilbertBlockL2 U) D) * (‖H‖ / σ) := by
          exact mul_le_mul_of_nonneg_left hL2 hC

noncomputable def responseEnergyShearFamily {U : Set (Vec 2)}
    (hU : MeasurableSet U) (σ : ℝ) (hσ : 0 < σ)
    (D : EnergyHilbertData (H := HilbertBlockL2 U)) :
    ResponseCoefficient U →L[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) := by
  let L : ResponseCoefficient U →ₗ[ℝ]
      (EnergyCarrier (H := HilbertBlockL2 U) D →L[ℝ]
        EnergyCarrier (H := HilbertBlockL2 U) D) :=
    responseEnergyShearFamilyLinear hU σ hσ D
  let C : ℝ := responseEnergyUpCLMNorm (H := HilbertBlockL2 U) D *
    responseEnergyDownCLMNorm (H := HilbertBlockL2 U) D / σ
  have hbound : ∀ H : ResponseCoefficient U,
      ‖L H‖ ≤ C * ‖H‖ := by
    intro H
    change ‖responseEnergyShearFamilyLinear hU σ hσ D H‖ ≤
      (responseEnergyUpCLMNorm (H := HilbertBlockL2 U) D *
        responseEnergyDownCLMNorm (H := HilbertBlockL2 U) D / σ) * ‖H‖
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      responseEnergyShearFamilyLinear_norm_le hU σ hσ D H
  exact @LinearMap.mkContinuous ℝ ℝ (ResponseCoefficient U)
    (EnergyCarrier (H := HilbertBlockL2 U) D →L[ℝ]
      EnergyCarrier (H := HilbertBlockL2 U) D)
    _ _ _ _ _ _ (RingHom.id ℝ) L C hbound

/-- Pointwise form of the dimension-free bound for the fixed-frame shear. -/
theorem responseFrameEnergyShearFamily_apply_norm_le {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k H : ResponseCoefficient U)
    (z : EnergyCarrier (responseEnergyHilbertData
      ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization))) :
    ‖responseEnergyShearFamilyLinear hU σ hσ
        (responseEnergyHilbertData
          ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)) H z‖ ≤
      (‖H‖ / ν) * ‖z‖ := by
  let M := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k
  let D := responseEnergyHilbertData (M.toMuHilbertRealization)
  let A := responseEnergyShearFamilyLinear hU σ hσ D H
  have hout : A z = ULift.up (responseShearL2Operator σ hσ H z.down) := by
    change responseEnergyConjugateOperator D (responseShearL2Operator σ hσ H) z = _
    exact responseEnergyConjugateOperator_apply D _ z
  have henergy := responseFrameMu_shearOperator_energy_bound
    hU hvol ν σ hν hσ k H z.down
  change D.energy (responseShearL2Operator σ hσ H z.down)
      (responseShearL2Operator σ hσ H z.down) ≤
    (‖H‖ / ν) ^ 2 * D.energy z.down z.down at henergy
  have houtNorm : ‖A z‖ ^ 2 =
      D.energy (responseShearL2Operator σ hσ H z.down)
        (responseShearL2Operator σ hσ H z.down) := by
    rw [hout]
    simpa using (energyCarrier_norm_sq D
      (ULift.up (responseShearL2Operator σ hσ H z.down)))
  have hzNorm : ‖z‖ ^ 2 = D.energy z.down z.down := energyCarrier_norm_sq D z
  have hcoef : 0 ≤ ‖H‖ / ν := div_nonneg (norm_nonneg _) hν.le
  have hnonnegA : 0 ≤ ‖A z‖ := norm_nonneg _
  have hnonnegZ : 0 ≤ ‖z‖ := norm_nonneg _
  have hsq : ‖A z‖ ^ 2 ≤ (‖H‖ / ν) ^ 2 * ‖z‖ ^ 2 := by
    calc
      ‖A z‖ ^ 2 = D.energy (responseShearL2Operator σ hσ H z.down)
          (responseShearL2Operator σ hσ H z.down) := houtNorm
      _ ≤ (‖H‖ / ν) ^ 2 * D.energy z.down z.down := henergy
      _ = (‖H‖ / ν) ^ 2 * ‖z‖ ^ 2 := by rw [← hzNorm]
  apply (sq_le_sq₀ hnonnegA (mul_nonneg hcoef hnonnegZ)).1
  calc
    ‖A z‖ ^ 2 ≤ (‖H‖ / ν) ^ 2 * ‖z‖ ^ 2 := hsq
    _ = ((‖H‖ / ν) * ‖z‖) ^ 2 := by ring

/-- The coefficient-indexed family satisfies the dimension-free operator
bound `‖C_H‖ ≤ ‖H‖∞/ν` in the fixed frame-energy norm. -/
theorem responseFrameEnergyShearFamilyLinear_norm_le {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k H : ResponseCoefficient U) :
    ‖responseEnergyShearFamilyLinear hU σ hσ
        (responseEnergyHilbertData
          ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)) H‖ ≤
      ‖H‖ / ν := by
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hν.le) ?_
  intro z
  exact responseFrameEnergyShearFamily_apply_norm_le
    hU hvol ν σ hν hσ k H z

/-- The coefficient-indexed family as a continuous linear map into operators
on one fixed frame-energy Hilbert space. -/
noncomputable def responseFrameEnergyShearFamily {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) :
    ResponseCoefficient U →L[ℝ]
      (EnergyCarrier (responseEnergyHilbertData
        ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)) →L[ℝ]
        EnergyCarrier (responseEnergyHilbertData
          ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization))) := by
  let D := responseEnergyHilbertData
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)
  let L : ResponseCoefficient U →ₗ[ℝ]
      (EnergyCarrier D →L[ℝ] EnergyCarrier D) :=
    responseEnergyShearFamilyLinear hU σ hσ D
  have hbound : ∀ H : ResponseCoefficient U, ‖L H‖ ≤ (1 / ν) * ‖H‖ := by
    intro H
    have hLin := responseFrameEnergyShearFamilyLinear_norm_le
      hU hvol ν σ hν hσ k H
    calc
      ‖L H‖ ≤ ‖H‖ / ν := by simpa [L, D] using hLin
      _ = (1 / ν) * ‖H‖ := by ring
  exact @LinearMap.mkContinuous ℝ ℝ (ResponseCoefficient U)
    (EnergyCarrier (H := HilbertBlockL2 U) D →L[ℝ]
      EnergyCarrier (H := HilbertBlockL2 U) D)
    _ _ _ _ _ _ (RingHom.id ℝ) L (1 / ν) hbound

/-- The doubled response energy associated with the fixed-frame coefficient. -/
noncomputable def responseFrameEnergy {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) (H : ResponseCoefficient U) : ℝ :=
  2 * (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + H)).toMuHilbertRealization.muCandidate P

noncomputable def responseFrameEnergyData {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) :
    EnergyHilbertData (H := HilbertBlockL2 U) :=
  responseEnergyHilbertData
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)

noncomputable def responseFrameEnergyVariationSpace {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) :
    ClosedSubmodule ℝ (EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k)) :=
  responseEnergyCorrectionSpace
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization)
    (responseFrameEnergyData hU hvol ν σ hν hσ k)

noncomputable def responseFrameEnergyBaseMinimizer {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) :
    EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k) :=
  responseEnergyUp (responseFrameEnergyData hU hvol ν σ hν hσ k)
    ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap P)

theorem responseFrameEnergyShearFamily_pairwise_nilpotent {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U)
    (H K : ResponseCoefficient U) :
    responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H ∘L
      responseFrameEnergyShearFamily hU hvol ν σ hν hσ k K = 0 := by
  change responseEnergyShearFamilyLinear hU σ hσ
      (responseFrameEnergyData hU hvol ν σ hν hσ k) H ∘L
    responseEnergyShearFamilyLinear hU σ hσ
      (responseFrameEnergyData hU hvol ν σ hν hσ k) K = 0
  exact responseEnergyShearFamilyLinear_pairwise_nilpotent hU σ hσ
    (responseFrameEnergyData hU hvol ν σ hν hσ k) H K

private theorem responseFrameEnergyShearMap_down {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient U)
    (z : EnergyCarrier (responseEnergyHilbertData
      ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization))) :
    (nilpotentShearMap
      (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H) 1 z).down =
      z.down + responseShearL2Operator σ hσ H z.down := by
  simp [nilpotentShearMap, responseFrameEnergyShearFamily,
    responseEnergyShearFamilyLinear, responseEnergyConjugateOperator_apply]
  rfl

private theorem responseEnergyMinimizerDifference_mem {U : Set (Vec 2)}
    {a₀ a₁ : CoeffField 2}
    (M₀ : MuHilbertRealization U a₀) (M₁ : MuHilbertRealization U a₁)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (hCorr : M₁.correctionSpace.correctionSpace =
      M₀.correctionSpace.correctionSpace)
    (hConst : M₁.constantField = M₀.constantField) (P : BlockVec 2) :
    responseEnergyUp D (M₁.minimizerMap P) -
      responseEnergyUp D (M₀.minimizerMap P) ∈ responseEnergyCorrectionSpace M₀ D := by
  apply (responseEnergyCorrectionSpace_mem_iff M₀ D _).2
  change M₁.minimizerMap P - M₀.minimizerMap P ∈
    M₀.correctionSpace.correctionSpace
  have h₁ := M₁.sub_minimizerMap_apply_mem P
  rw [hCorr, hConst] at h₁
  have h₀ := M₀.sub_minimizerMap_apply_mem P
  have hEq : M₁.minimizerMap P - M₀.minimizerMap P =
      (M₁.minimizerMap P - M₀.constantField P) -
        (M₀.minimizerMap P - M₀.constantField P) := by abel
  rw [hEq]
  exact M₀.correctionSpace.correctionSpace.toSubmodule.sub_mem h₁ h₀

private theorem responseEnergyCorrection_affine_mem {U : Set (Vec 2)}
    {a₀ a₁ : CoeffField 2}
    (M₀ : MuHilbertRealization U a₀) (M₁ : MuHilbertRealization U a₁)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (hCorr : M₁.correctionSpace.correctionSpace =
      M₀.correctionSpace.correctionSpace)
    (hConst : M₁.constantField = M₀.constantField) (P : BlockVec 2)
    (z s : EnergyCarrier D)
    (hz : z.down - s.down ∈ M₀.correctionSpace.correctionSpace)
    (hs : s.down - M₀.constantField P ∈ M₀.correctionSpace.correctionSpace) :
    z.down - M₁.constantField P ∈ M₁.correctionSpace.correctionSpace := by
  rw [hConst, hCorr]
  have hEq : z.down - M₀.constantField P =
      (z.down - s.down) + (s.down - M₀.constantField P) := by abel
  rw [hEq]
  exact M₀.correctionSpace.correctionSpace.toSubmodule.add_mem hz hs

private theorem responseFrameEnergy_shearFactor {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient U)
    (X : EnergyCarrier (responseFrameEnergyData hU hvol ν σ hν hσ k)) :
    ‖nilpotentShearMap (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H) 1 X‖ ^ 2 =
      ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + H)).toMuHilbertRealization).energyBilin
        X.down X.down := by
  let M₀ := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
  let M₁sys := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + H)
  let M₁ := M₁sys.toMuHilbertRealization
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  calc
    ‖nilpotentShearMap (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H) 1 X‖ ^ 2 =
        D.energy (nilpotentShearMap
          (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H) 1 X).down
          (nilpotentShearMap
            (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k H) 1 X).down :=
      energyCarrier_norm_sq D _
    _ = D.energy (X.down + responseShearL2Operator σ hσ H X.down)
          (X.down + responseShearL2Operator σ hσ H X.down) := by
      rw [responseFrameEnergyShearMap_down hU hvol ν σ hν hσ k H X]
    _ = M₁.energyBilin X.down X.down := by
      change M₀.energyBilin
        (X.down + responseShearL2Operator σ hσ H X.down)
        (X.down + responseShearL2Operator σ hσ H X.down) = _
      simpa [M₀, M₁, D] using
        responseFrameMu_energy_shear_identity hU hvol ν σ hν hσ k H X.down

private theorem responseEnergy_linearMinimum_le_candidate {U : Set (Vec 2)}
    {a : CoeffField 2} (M : MuHilbertRealization U a)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (V : ClosedSubmodule ℝ (EnergyCarrier D))
    (C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D))
    (S : EnergyCarrier D) (H : ResponseCoefficient U)
    (hNil : ∀ A B, C A ∘L C B = 0) (P : BlockVec 2)
    (W : EnergyCarrier D) (hW : W - S ∈ V.toSubmodule)
    (hWmap : W.down = M.minimizerMap P)
    (hFactor : ∀ X : EnergyCarrier D,
      ‖nilpotentShearMap (C H) 1 X‖ ^ 2 = M.energyBilin X.down X.down) :
    linearShearMinimum V C S H hNil ≤ 2 * M.muCandidate P := by
  have hMin := linearShearMinimum_minimizes V C S W H hNil hW
  have htwoMu : 2 * M.muCandidate P =
      M.energyBilin (M.minimizerMap P) (M.minimizerMap P) := by
    change 2 * ((1 / 2 : ℝ) *
      M.energyBilin (M.minimizerMap P) (M.minimizerMap P)) = _
    ring
  calc
    linearShearMinimum V C S H hNil ≤
        ‖nilpotentShearMap (C H) 1 W‖ ^ 2 := hMin
    _ = M.energyBilin (M.minimizerMap P) (M.minimizerMap P) := by
        rw [← hWmap]
        exact hFactor W
    _ = 2 * M.muCandidate P := htwoMu.symm

private theorem responseEnergy_candidate_le_linearMinimum {U : Set (Vec 2)}
    {a : CoeffField 2} (M : MuHilbertRealization U a)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (V : ClosedSubmodule ℝ (EnergyCarrier D))
    (C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D))
    (S : EnergyCarrier D) (H : ResponseCoefficient U)
    (hNil : ∀ A B, C A ∘L C B = 0) (P : BlockVec 2)
    (Z : EnergyCarrier D)
    (hZaff : Z.down - M.constantField P ∈ M.correctionSpace.correctionSpace)
    (hMinEq : linearShearMinimum V C S H hNil =
      ‖nilpotentShearMap (C H) 1 Z‖ ^ 2)
    (hFactor : ∀ X : EnergyCarrier D,
      ‖nilpotentShearMap (C H) 1 X‖ ^ 2 = M.energyBilin X.down X.down) :
    2 * M.muCandidate P ≤ linearShearMinimum V C S H hNil := by
  have hCoarse := M.muCandidate_le_quadraticEnergy P Z.down hZaff
  have hMu : 2 * M.muCandidate P ≤ M.energyBilin Z.down Z.down := by
    change M.muCandidate P ≤ (1 / 2 : ℝ) * M.energyBilin Z.down Z.down at hCoarse
    nlinarith
  calc
    2 * M.muCandidate P ≤ M.energyBilin Z.down Z.down := hMu
    _ = ‖nilpotentShearMap (C H) 1 Z‖ ^ 2 := (hFactor Z).symm
    _ = linearShearMinimum V C S H hNil := hMinEq.symm

private theorem responseEnergy_linearShear_eq_candidate {U : Set (Vec 2)}
    {a : CoeffField 2} (M : MuHilbertRealization U a)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (V : ClosedSubmodule ℝ (EnergyCarrier D))
    (C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D))
    (S : EnergyCarrier D) (H : ResponseCoefficient U)
    (hNil : ∀ A B, C A ∘L C B = 0) (P : BlockVec 2)
    (W Z : EnergyCarrier D)
    (hWsub : W - S ∈ V.toSubmodule) (hWmap : W.down = M.minimizerMap P)
    (hZaff : Z.down - M.constantField P ∈ M.correctionSpace.correctionSpace)
    (hZmin : linearShearMinimum V C S H hNil =
      ‖nilpotentShearMap (C H) 1 Z‖ ^ 2)
    (hFactor : ∀ X : EnergyCarrier D,
      ‖nilpotentShearMap (C H) 1 X‖ ^ 2 = M.energyBilin X.down X.down) :
    2 * M.muCandidate P = linearShearMinimum V C S H hNil := by
  have hMinLe := responseEnergy_linearMinimum_le_candidate M D V C S H
    hNil P W hWsub hWmap hFactor
  have hMuLe := responseEnergy_candidate_le_linearMinimum M D V C S H
    hNil P Z hZaff hZmin hFactor
  exact le_antisymm hMuLe hMinLe

private theorem responseEnergy_Mu_minimum_eq {U : Set (Vec 2)}
    {a₀ a₁ : CoeffField 2}
    (M₀ : MuHilbertRealization U a₀) (M₁ : MuHilbertRealization U a₁)
    (D : EnergyHilbertData (H := HilbertBlockL2 U))
    (V : ClosedSubmodule ℝ (EnergyCarrier D))
    (C : ResponseCoefficient U →L[ℝ] (EnergyCarrier D →L[ℝ] EnergyCarrier D))
    (S : EnergyCarrier D) (H : ResponseCoefficient U)
    (hNil : ∀ A B, C A ∘L C B = 0) (P : BlockVec 2)
    (hCorr : M₁.correctionSpace.correctionSpace = M₀.correctionSpace.correctionSpace)
    (hConst : M₁.constantField = M₀.constantField)
    (hV : V = responseEnergyCorrectionSpace M₀ D)
    (hS : S = responseEnergyUp D (M₀.minimizerMap P))
    (hFactor : ∀ X : EnergyCarrier D,
      ‖nilpotentShearMap (C H) 1 X‖ ^ 2 = M₁.energyBilin X.down X.down) :
    2 * M₁.muCandidate P = linearShearMinimum V C S H hNil := by
  let W := responseEnergyUp D (M₁.minimizerMap P)
  let Z := linearShearMinimizer V C S H hNil
  have hWsub : W - S ∈ V.toSubmodule := by
    rw [hV, hS]
    exact responseEnergyMinimizerDifference_mem M₀ M₁ D hCorr hConst P
  have hWmap : W.down = M₁.minimizerMap P := rfl
  have hZsub : Z - S ∈ V.toSubmodule := linearShearMinimizer_sub_mem V C S H hNil
  have hZvar : Z.down - S.down ∈ M₀.correctionSpace.correctionSpace := by
    have hmem : Z - S ∈ responseEnergyCorrectionSpace M₀ D := by
      rw [← hV]
      exact hZsub
    have h := (responseEnergyCorrectionSpace_mem_iff M₀ D (Z - S)).mp hmem
    have hDown : (Z - S).down = Z.down - S.down := rfl
    rw [hDown] at h
    exact h
  have hSaff : S.down - M₀.constantField P ∈ M₀.correctionSpace.correctionSpace := by
    rw [hS]
    exact M₀.sub_minimizerMap_apply_mem P
  have hZaff := responseEnergyCorrection_affine_mem M₀ M₁ D
    hCorr hConst P Z S hZvar hSaff
  have hZmin : linearShearMinimum V C S H hNil =
      ‖nilpotentShearMap (C H) 1 Z‖ ^ 2 := rfl
  exact responseEnergy_linearShear_eq_candidate M₁ D V C S H hNil P W Z
    hWsub hWmap hZaff hZmin hFactor

private theorem responseSystems_sameCorrectionSpace {U : Set (Vec 2)}
    {a₀ a₁ : CoeffField 2}
    (M₀ : MuOperatorSystemData U a₀) (M₁ : MuOperatorSystemData U a₁)
    (h : M₁.correctionSpace = M₀.correctionSpace)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    M₁.toMuHilbertRealization.correctionSpace.correctionSpace =
      M₀.toMuHilbertRealization.correctionSpace.correctionSpace := by
  change M₁.correctionSpace.correctionSpace = M₀.correctionSpace.correctionSpace
  rw [h]

private theorem responseSystems_sameConstantField {U : Set (Vec 2)}
    {a₀ a₁ : CoeffField 2}
    (M₀ : MuOperatorSystemData U a₀) (M₁ : MuOperatorSystemData U a₁)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    M₁.toMuHilbertRealization.constantField = M₀.toMuHilbertRealization.constantField := by
  change blockVecToHilbertBlockL2Const (U := U) =
    blockVecToHilbertBlockL2Const (U := U)
  rfl

/-- The Coarse minimized response is the linear-family minimum on the fixed
energy Hilbert space. This is the coefficient dependence transfer. -/
theorem responseFrameEnergy_eq_linearShearMinimum {U : Set (Vec 2)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (P : BlockVec 2) (H : ResponseCoefficient U) :
    responseFrameEnergy hU hvol ν σ hν hσ k P H =
      linearShearMinimum
        (responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k)
        (responseFrameEnergyShearFamily hU hvol ν σ hν hσ k)
        (responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P) H
        (responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k) := by
  let M₀sys := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k
  let M₀ := M₀sys.toMuHilbertRealization
  let M₁raw := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + H)
  let M₁ := M₁raw.toMuHilbertRealization
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k
  have hSysCorr : M₁raw.correctionSpace = M₀sys.correctionSpace := by
    change (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData =
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData
    rfl
  have hCorr : M₁.correctionSpace.correctionSpace = M₀.correctionSpace.correctionSpace :=
    responseSystems_sameCorrectionSpace M₀sys M₁raw hSysCorr
  have hConst : M₁.constantField = M₀.constantField :=
    responseSystems_sameConstantField M₀sys M₁raw
  have hV : V = responseEnergyCorrectionSpace M₀ D := by rfl
  have hS : S = responseEnergyUp D (M₀.minimizerMap P) := by rfl
  have hFactor (X : EnergyCarrier D) :
      ‖nilpotentShearMap (C H) 1 X‖ ^ 2 = M₁.energyBilin X.down X.down := by
    exact responseFrameEnergy_shearFactor hU hvol ν σ hν hσ k H X
  change 2 * M₁.muCandidate P = linearShearMinimum V C S H hNil
  exact responseEnergy_Mu_minimum_eq M₀ M₁ D V C S H hNil P
    hCorr hConst hV hS hFactor

end

end ASDExplicitGamma.Response
