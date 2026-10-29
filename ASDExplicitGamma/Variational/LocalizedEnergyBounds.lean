module

public import ASDExplicitGamma.Variational.LocalizedBlockSpace

/-! Exact gradient and pure-flux energy bounds in physical viscosity/frame units. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
noncomputable section

 theorem hilbertL2_norm_sq_integral {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : Lp E 2 μ) :
    ‖X‖^2 = ∫ x, ‖X x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

 theorem hilbertPureSecond_toBlockVec (y : HilbertVec 2) :
    (hilbertPureSecond y).toBlockVec = (0,y.toVec) := by
  apply Prod.ext
  · funext i
    change (PiLp.single (β := fun _ : Fin 2 => HilbertVec 2) 2 1 y) 0 i = 0
    simp only [PiLp.single_apply]
    norm_num
  · funext i
    change (PiLp.single (β := fun _ : Fin 2 => HilbertVec 2) 2 1 y) 1 i = y i
    simp only [PiLp.single_apply, ite_true]

 theorem hilbertVec_vecNormSq (x : HilbertVec 2) : vecNormSq x.toVec = ‖x‖^2 := by
  simp only [vecNormSq, vecDot, HilbertVec.toVec]
  calc
    (∑ i, x.ofLp i * x.ofLp i) = ∑ i, x.ofLp i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ‖x‖^2 := (HilbertVec.norm_sq_eq_sum_sq x).symm

 theorem frameDensity_hilbert_first_lower (ν σ κ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (X : HilbertBlockVec 2) :
    (ν/σ)*‖X.potential‖^2 ≤ responseFrameEnergyDensity ν σ κ X.toBlockVec := by
  unfold responseFrameEnergyDensity
  have hn := mul_nonneg (div_nonneg hσ.le hν.le)
    (vecNormSq_nonneg (X.toBlockVec.2-(κ/σ) • matVecMul responsePlanarJ X.toBlockVec.1))
  have he : vecNormSq X.toBlockVec.1 = ‖X.potential‖^2 := by
    rw [HilbertBlockVec.toBlockVec]
    exact hilbertVec_vecNormSq X.potential
  rw [he]
  exact le_add_of_nonneg_right hn

 theorem frameDensity_hilbert_pureSecond (ν σ κ : ℝ) (Y : HilbertVec 2) :
    responseFrameEnergyDensity ν σ κ (hilbertPureSecond Y).toBlockVec = (σ/ν)*‖Y‖^2 := by
  rw [hilbertPureSecond_toBlockVec]
  simp only [responseFrameEnergyDensity, matVecMul_zero, smul_zero, sub_zero]
  rw [show vecNormSq (0 : Vec 2) = 0 by simp [vecNormSq, vecDot], mul_zero, zero_add,
    hilbertVec_vecNormSq]

variable {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]

 theorem frameDensity_hilbert_integrable (hU : MeasurableSet U) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    Integrable (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (X x).toBlockVec)
      (volumeMeasureOn U) := by
  let F := hilbertBlockL2ToBlockL2 X
  let S : BlockState 2 := ⟨fun x => (F x).1,fun x => (F x).2⟩
  have hmem : MemBlockL2 U S.eval := F.property
  have hp := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hmem hmem
    (responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k)
  apply hp.congr
  filter_upwards [coeFn_hilbertBlockL2ToBlockL2 X] with x hx
  change blockVecDot (F x) (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x) (F x)) = _
  rw [hx]
  exact (responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ (responseCoefficientExtension k x) hν hσ _).symm

 theorem frameEnergy_eq_hilbert_integral (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    (responseFrameEnergyData hU hvol ν σ hν hσ k).energy X X =
      (volume U).toReal⁻¹*∫ x, responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (X x).toBlockVec ∂volumeMeasureOn U := by
  rw [show (responseFrameEnergyData hU hvol ν σ hν hσ k).energy X X =
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin X X from rfl,
    responseFrameMu_energy_eq_volumeAverage_density]
  unfold volumeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [coeFn_hilbertBlockL2ToBlockL2 X] with x hx
  rw [hx]

 theorem hilbertFirstProjection_energy_bound (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U) (X : HilbertBlockL2 U) :
    (ν/σ)*‖hilbertFirstProjection U X‖^2 ≤ (volume U).toReal*
      (responseFrameEnergyData hU hvol ν σ hν hσ k).energy X X := by
  have hproj := (PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 0 : HilbertBlockVec 2 →L[ℝ] HilbertVec 2).coeFn_compLpL X
  have hproj' : (fun x : Vec 2 => (hilbertFirstProjection U X) x) =ᵐ[volumeMeasureOn U]
      (fun x => ((PiLp.proj 2 (fun _ : Fin 2 => HilbertVec 2) 0 :
        HilbertBlockVec 2 →L[ℝ] HilbertVec 2) (X x))) := by
    simpa only [hilbertFirstProjection] using hproj
  have he : (∫ x, ‖(X x).potential‖^2 ∂volumeMeasureOn U)=‖hilbertFirstProjection U X‖^2 := by
    rw [hilbertL2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [hproj'] with x hx
    rw [hx]
    rfl
  have hint : Integrable (fun x => ‖(X x).potential‖^2) (volumeMeasureOn U) := by
    have ht := L2.integrable_inner (𝕜 := ℝ) (hilbertFirstProjection U X) (hilbertFirstProjection U X)
    apply ht.congr
    filter_upwards [hproj'] with x hx
    rw [real_inner_self_eq_norm_sq,hx]
    rfl
  have hle := integral_mono_ae (hint.const_mul (ν/σ)) (frameDensity_hilbert_integrable hU ν σ hν hσ k X)
    (Filter.Eventually.of_forall fun x => frameDensity_hilbert_first_lower ν σ (responseCoefficientExtension k x) hν hσ (X x))
  rw [integral_const_mul,he] at hle
  rw [frameEnergy_eq_hilbert_integral]
  simpa only [← mul_assoc,mul_inv_cancel₀ hvol.ne',one_mul] using hle

 theorem hilbertPureSecond_energy_eq (hU : MeasurableSet U) (hvol : 0 < (volume U).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U)
    (Y : HilbertVectorL2 U) :
    (responseFrameEnergyData hU hvol ν σ hν hσ k).energy
        (hilbertPureSecondL2 U Y) (hilbertPureSecondL2 U Y) =
      (volume U).toReal⁻¹ * (σ/ν) * ‖Y‖^2 := by
  rw [frameEnergy_eq_hilbert_integral hU hvol ν σ hν hσ k]
  have hcomp := hilbertPureSecond.toContinuousLinearMap.coeFn_compLpL Y
  have hcomp' : (fun x : Vec 2 => hilbertPureSecondL2 U Y x) =ᵐ[volumeMeasureOn U]
      (fun x => hilbertPureSecond.toContinuousLinearMap (Y x)) := by
    simpa only [hilbertPureSecondL2] using hcomp
  have hpoint : (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x)
      ((hilbertPureSecondL2 U Y x).toBlockVec)) =ᵐ[volumeMeasureOn U]
      (fun x => (σ/ν)*‖Y x‖^2) := by
    filter_upwards [hcomp'] with x hx
    rw [hx]
    exact frameDensity_hilbert_pureSecond ν σ (responseCoefficientExtension k x) (Y x)
  rw [show (∫ x, responseFrameEnergyDensity ν σ (responseCoefficientExtension k x)
      ((hilbertPureSecondL2 U Y x).toBlockVec) ∂volumeMeasureOn U) =
      ∫ x, (σ/ν)*‖Y x‖^2 ∂volumeMeasureOn U from integral_congr_ae hpoint,
    integral_const_mul, hilbertL2_norm_sq_integral]
  ring

end
end ASDExplicitGamma.Variational
