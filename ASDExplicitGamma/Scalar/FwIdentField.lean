module

public import ASDExplicitGamma.Scalar.FwIdentHilbert
public import ASDExplicitGamma.Scalar.FwIdentPriv
public import ASDExplicitGamma.Scalar.DualMaximizer

/-! T4, field part: energy and pairing of a scalar variation field in Hilbert terms; every
scalar variation of the Hilbert pair `(x,s)` is realized by a field. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

section Field

variable (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
  (k : ResponseCoefficient (openCubeSet Q))

/-- The literal field energy of a pair of `L²` fields, in Hilbert terms. -/
theorem fw_field_energy {f g : Vec 2 → Vec 2} (hf : MemVectorL2 (openCubeSet Q) f)
    (hg : MemVectorL2 (openCubeSet Q) g) :
    scalarFieldEnergy ν σ k (fun x => (f x, g x)) =
      (volume (openCubeSet Q)).toReal⁻¹ *
        ((ν / σ) * ‖toHilbertVectorL2OfVecField hf‖ ^ 2 + (ν / σ)⁻¹ *
          ‖toHilbertVectorL2OfVecField hg -
            physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hf)‖ ^ 2) := by
  let U := openCubeSet Q
  let p := toHilbertVectorL2OfVecField hf
  let hwLp := hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ k p)
  let wField : Vec 2 → Vec 2 := fun x => hwLp x
  have hw : MemVectorL2 U wField := by
    change MeasureTheory.MemLp (fun x => hwLp x) 2 (volumeMeasureOn U)
    exact MeasureTheory.Lp.memLp hwLp
  have hr : MemVectorL2 U (g - wField) := hg.sub hw
  have hW : toHilbertVectorL2OfVecField hw = physicalPositiveShear Q σ hσ k p := by
    calc
      toHilbertVectorL2OfVecField hw = vectorL2ToHilbertVectorL2 (toVectorL2 hw) :=
        (vectorL2ToHilbertVectorL2_toVectorL2 hw).symm
      _ = vectorL2ToHilbertVectorL2 hwLp := by
        rw [show toVectorL2 hw = hwLp from MeasureTheory.Lp.toLp_coeFn hwLp hw]
      _ = _ := vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 _
  have hR : toHilbertVectorL2OfVecField hr =
      toHilbertVectorL2OfVecField hg - physicalPositiveShear Q σ hσ k p := by
    rw [toHilbertVectorL2OfVecField_sub hg hw, hW]
  have hpPlain : hilbertVectorL2ToVectorL2 p =ᵐ[volumeMeasureOn U] f := by
    rw [show p = toHilbertVectorL2OfVecField hf from rfl,
      hilbertVectorL2ToVectorL2_toHilbertVectorL2 hf]
    exact coeFn_toVectorL2 hf
  have hWPlain := fw_shear_toPlain_ae Q σ hσ k p
  have hDensity : (fun x => responseFrameEnergyDensity ν σ
        (responseCoefficientExtension k x) (f x, g x)) =ᵐ[volumeMeasureOn U]
        fun x => (ν / σ) * vecNormSq (f x) + (ν / σ)⁻¹ * vecNormSq ((g - wField) x) := by
    filter_upwards [hWPlain, hpPlain] with x hxW hxp
    simp only [responseFrameEnergyDensity]
    have hWf : wField x = ((responseCoefficientExtension k x / σ) •
          matVecMul responsePlanarJ (f x)) := by
      calc wField x = (responseCoefficientExtension k x / σ) •
            matVecMul responsePlanarJ (hilbertVectorL2ToVectorL2 p x) := hxW
        _ = _ := by rw [hxp]
    rw [Pi.sub_apply, hWf, inv_div]
  have hfSqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (f x)) U := by
    simpa [vecNormSq, MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (integrableOn_vecDot_of_memVectorL2 hf hf)
  have hrSqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq ((g - wField) x)) U := by
    simpa [vecNormSq, MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (integrableOn_vecDot_of_memVectorL2 hr hr)
  have hfirstInt : MeasureTheory.Integrable (fun x => (ν / σ) * vecNormSq (f x))
      (volumeMeasureOn U) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hfSqInt.const_mul (ν / σ)
  have hsecondInt : MeasureTheory.Integrable
      (fun x => (ν / σ)⁻¹ * vecNormSq ((g - wField) x)) (volumeMeasureOn U) := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using hrSqInt.const_mul ((ν / σ)⁻¹)
  have hIntegral : ∫ x in U, responseFrameEnergyDensity ν σ
          (responseCoefficientExtension k x) (f x, g x) ∂MeasureTheory.volume =
        (ν / σ) * ‖p‖ ^ 2 + (ν / σ)⁻¹ * ‖toHilbertVectorL2OfVecField hr‖ ^ 2 := by
    rw [MeasureTheory.integral_congr_ae hDensity]
    rw [MeasureTheory.integral_add hfirstInt hsecondInt]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      ← fw_hilbertVectorL2_norm_sq_integral U f hf,
      ← fw_hilbertVectorL2_norm_sq_integral U (g - wField) hr]
  unfold scalarFieldEnergy volumeAverage
  rw [hIntegral, hR]

/-- The source pairing with a field, in Hilbert terms. -/
theorem fw_pairing {w f : Vec 2 → Vec 2} (hw : MemVectorL2 (openCubeSet Q) w)
    (hf : MemVectorL2 (openCubeSet Q) f) (g : Vec 2 → Vec 2) :
    scalarSourcePairing (openCubeSet Q) w (fun x => (f x, g x)) =
      (volume (openCubeSet Q)).toReal⁻¹ *
        ⟪toHilbertVectorL2OfVecField hw, toHilbertVectorL2OfVecField hf⟫_ℝ := by
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hw hf]
  unfold scalarSourcePairing volumeAverage
  rfl

/-- Every Hilbert pair `(x,s) ∈ X × K` is the class of a scalar variation field. -/
theorem fw_variation_of_hilbert
    (x : (physicalPotentialSpace Q).toSubmodule)
    (s : (physicalSolenoidalSpace Q).toSubmodule) :
    ∃ (f g : Vec 2 → Vec 2) (hf : MemVectorL2 (openCubeSet Q) f)
      (hg : MemVectorL2 (openCubeSet Q) g),
      ScalarVariation (openCubeSet Q) (fun y => (f y, g y)) ∧
        toHilbertVectorL2OfVecField hf = (x : HilbertVectorL2 (openCubeSet Q)) ∧
        toHilbertVectorL2OfVecField hg = (s : HilbertVectorL2 (openCubeSet Q)) := by
  obtain ⟨u, hu⟩ := (PotentialSolenoidalExact.mem_potentialZeroTrace_iff
    (x : HilbertVectorL2 (openCubeSet Q))).1 x.2
  let g : Vec 2 → Vec 2 := hilbertVectorL2ToVectorL2 (s : HilbertVectorL2 (openCubeSet Q))
  have hg : MemVectorL2 (openCubeSet Q) g := by
    change MeasureTheory.MemLp
      (fun y => hilbertVectorL2ToVectorL2 (s : HilbertVectorL2 (openCubeSet Q)) y)
      2 (volumeMeasureOn (openCubeSet Q))
    exact MeasureTheory.Lp.memLp (hilbertVectorL2ToVectorL2 (s : HilbertVectorL2 (openCubeSet Q)))
  have hgs : toHilbertVectorL2OfVecField hg = (s : HilbertVectorL2 (openCubeSet Q)) := by
    simpa [g, hg] using
      (fw_toHilbertVectorL2OfVecField_hilbertVectorL2ToVectorL2
        (s : HilbertVectorL2 (openCubeSet Q)))
  have hfx : toHilbertVectorL2OfVecField u.toH1Function.grad_memVectorL2 =
      (x : HilbertVectorL2 (openCubeSet Q)) := hu
  have hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) g := by
    intro φ
    have h0 := (PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff
      (s : HilbertVectorL2 (openCubeSet Q))).1 s.2 φ
    rw [← hgs, show φ.gradToHilbertVectorL2 =
      toHilbertVectorL2OfVecField φ.grad_memVectorL2 from rfl,
      inner_toHilbertVectorL2OfVecField_eq_integral hg φ.grad_memVectorL2] at h0
    exact h0
  exact ⟨u.toH1Function.grad, g, u.toH1Function.grad_memVectorL2, hg,
    ⟨memBlockL2_blockField u.toH1Function.grad_memVectorL2 hg, ⟨u, rfl⟩, hsol⟩, hfx, hgs⟩

end Field

end

end ASDExplicitGamma.Scalar
