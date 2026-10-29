module

public import ASDExplicitGamma.Scalar.FwIdentField

/-! T4: the pair-space OLD solution of the load `(0, w̃)` is the scalar OLD maximizer together
with its reciprocal flux. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem fw_inverse_of_operator {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (α : ℝ) (hα : 0 < α) (A : X →L[ℝ] Y) (v f : pureFluxPair (Y := Y) (X := X))
    (h : pureFluxBlockOperator α A v = f) : pureFluxBlockInverse α hα A f = v := by
  have := pureFluxBlockInverse_right α hα A
  rw [← h]
  exact DFunLike.congr_fun this v

theorem fw_block_apply {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (α : ℝ) (A : X →L[ℝ] Y) (y : Y) (x w : X) (h1 : α • y + A x = 0)
    (h2 : -(A.adjoint y) + α • x = w) :
    pureFluxBlockOperator α A (WithLp.toLp 2 (y, x)) = WithLp.toLp 2 ((0 : Y), w) := by
  apply WithLp.ofLp_injective 2
  rw [pureFluxBlockOperator_apply]
  exact Prod.ext h1 h2

/-- The potential-space element carrying a zero-trace gradient load. -/
def fwLoad (Q : TriadicCube 2) (u : H10Function (openCubeSet Q)) :
    (physicalPotentialSpace Q).toSubmodule :=
  ⟨u.toH1Function.gradToHilbertVectorL2, ⟨u, rfl⟩⟩

/-- The pair-space OLD solution of the load `(0, ∇u)`. -/
def fwPairSolution (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (u : H10Function (openCubeSet Q)) :
    pureFluxPair (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule) :=
  pureFluxBlockInverse (ν / σ) (div_pos hν hσ) (physicalProjectedCoefficient Q σ hσ k)
    (WithLp.toLp 2 ((0 : HilbertVectorL2 (openCubeSet Q)), fwLoad Q u))

theorem fw_projCoeff_apply (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (x' : (physicalPotentialSpace Q).toSubmodule) :
    physicalProjectedCoefficient Q σ hσ k x' =
      ((physicalSolenoidalSpace Q).toSubmodule)ᗮ.starProjection
        (physicalPositiveShear Q σ hσ k (x' : HilbertVectorL2 (openCubeSet Q))) := rfl

/-- The Hilbert-side maximizing pair of a scalar variation. -/
def fwX0 (Q : TriadicCube 2) {p : Vec 2 → Vec 2} (hp : MemVectorL2 (openCubeSet Q) p)
    (hpot : IsPotentialZeroTraceOn (openCubeSet Q) p) :
    (physicalPotentialSpace Q).toSubmodule :=
  ⟨toHilbertVectorL2OfVecField hp, fw_physicalField_memPotentialSpace Q hp hpot⟩

/-- The Hilbert-side solenoidal part of a scalar variation. -/
def fwS0 (Q : TriadicCube 2) {q : Vec 2 → Vec 2} (hq : MemVectorL2 (openCubeSet Q) q)
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) q) :
    (physicalSolenoidalSpace Q).toSubmodule :=
  ⟨toHilbertVectorL2OfVecField hq, fw_physicalField_memSolenoidalSpace Q hq hsol⟩

theorem fw_hmax (Q : TriadicCube 2) (ν σ : ℝ) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (u : H10Function (openCubeSet Q))
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k (fun x => u.toH1Function.grad x) Z)
    (hp : MemVectorL2 (openCubeSet Q) (fun x => (Z x).1))
    (hq : MemVectorL2 (openCubeSet Q) (fun x => (Z x).2)) :
    ∀ (x' : (physicalPotentialSpace Q).toSubmodule)
      (s' : (physicalSolenoidalSpace Q).toSubmodule),
      fwPhi (physicalSolenoidalSpace Q).toSubmodule (physicalPotentialSpace Q).toSubmodule
        (physicalPositiveShear Q σ hσ k) (ν / σ) (fwLoad Q u) x' s' ≤
      fwPhi (physicalSolenoidalSpace Q).toSubmodule (physicalPotentialSpace Q).toSubmodule
        (physicalPositiveShear Q σ hσ k) (ν / σ) (fwLoad Q u)
        (fwX0 Q hp hZ.1.2.1) (fwS0 Q hq hZ.1.2.2) := by
  let U := openCubeSet Q
  have hvol : 0 < (volume U).toReal := by
    dsimp [U]
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  have hw : MemVectorL2 U (fun x => u.toH1Function.grad x) := u.toH1Function.grad_memVectorL2
  have hwt : toHilbertVectorL2OfVecField hw = (fwLoad Q u : HilbertVectorL2 U) := rfl
  intro x' s'
  obtain ⟨f, g, hf, hg, hvar, hfx, hgs⟩ := fw_variation_of_hilbert Q x' s'
  have h := hZ.2 (fun y => (f y, g y)) hvar
  have hEZ : scalarFieldEnergy ν σ k Z = (volume U).toReal⁻¹ *
      ((ν / σ) * ‖toHilbertVectorL2OfVecField hp‖ ^ 2 + (ν / σ)⁻¹ *
        ‖toHilbertVectorL2OfVecField hq -
          physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hp)‖ ^ 2) :=
    fw_field_energy Q ν σ hσ k hp hq
  have hPZ : scalarSourcePairing U (fun x => u.toH1Function.grad x) Z =
      (volume U).toReal⁻¹ * ⟪toHilbertVectorL2OfVecField hw, toHilbertVectorL2OfVecField hp⟫_ℝ :=
    fw_pairing Q hw hp _
  rw [fw_pairing Q hw hf g, fw_field_energy Q ν σ hσ k hf hg, hfx, hgs, hwt] at h
  rw [hPZ, hEZ, hwt] at h
  have hV : 0 < (volume U).toReal⁻¹ := inv_pos.mpr hvol
  unfold fwPhi
  change _ ≤ 2 * ⟪(fwLoad Q u : HilbertVectorL2 U), toHilbertVectorL2OfVecField hp⟫_ℝ -
    (ν / σ) * ‖toHilbertVectorL2OfVecField hp‖ ^ 2 - (ν / σ)⁻¹ *
      ‖toHilbertVectorL2OfVecField hq -
        physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hp)‖ ^ 2
  have h' : (volume U).toReal⁻¹ * (2 * ⟪(fwLoad Q u : HilbertVectorL2 U), (x' : HilbertVectorL2 U)⟫_ℝ -
      (ν / σ) * ‖(x' : HilbertVectorL2 U)‖ ^ 2 - (ν / σ)⁻¹ *
        ‖(s' : HilbertVectorL2 U) - physicalPositiveShear Q σ hσ k (x' : HilbertVectorL2 U)‖ ^ 2) ≤
      (volume U).toReal⁻¹ * (2 * ⟪(fwLoad Q u : HilbertVectorL2 U), toHilbertVectorL2OfVecField hp⟫_ℝ -
    (ν / σ) * ‖toHilbertVectorL2OfVecField hp‖ ^ 2 - (ν / σ)⁻¹ *
      ‖toHilbertVectorL2OfVecField hq -
        physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hp)‖ ^ 2) := by
    linarith [h]
  exact le_of_mul_le_mul_left h' hV

theorem fw_flux_ae (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (Z : Vec 2 → BlockVec 2)
    (hp : MemVectorL2 (openCubeSet Q) (fun x => (Z x).1))
    (hq : MemVectorL2 (openCubeSet Q) (fun x => (Z x).2)) :
    hilbertVectorL2ToVectorL2 ((ν / σ)⁻¹ • (toHilbertVectorL2OfVecField hq -
        physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hp))) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k) Z x).2 := by
  let U := openCubeSet Q
  have hα : 0 < ν / σ := div_pos hν hσ
  have hpPlain : hilbertVectorL2ToVectorL2 (toHilbertVectorL2OfVecField hp) =ᵐ[volumeMeasureOn U]
      fun x => (Z x).1 := by
    rw [hilbertVectorL2ToVectorL2_toHilbertVectorL2 hp]
    exact coeFn_toVectorL2 hp
  have hqPlain : hilbertVectorL2ToVectorL2 (toHilbertVectorL2OfVecField hq) =ᵐ[volumeMeasureOn U]
      fun x => (Z x).2 := by
    rw [hilbertVectorL2ToVectorL2_toHilbertVectorL2 hq]
    exact coeFn_toVectorL2 hq
  have hWPlain := fw_shear_toPlain_ae Q σ hσ k (toHilbertVectorL2OfVecField hp)
  have hmap : hilbertVectorL2ToVectorL2 ((ν / σ)⁻¹ • (toHilbertVectorL2OfVecField hq -
        physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hp))) = (ν / σ)⁻¹ •
      (hilbertVectorL2ToVectorL2 (toHilbertVectorL2OfVecField hq) -
        hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ k
          (toHilbertVectorL2OfVecField hp))) := by
    rw [map_smul, map_sub]
  have hsm := MeasureTheory.Lp.coeFn_smul ((ν / σ)⁻¹)
    (hilbertVectorL2ToVectorL2 (toHilbertVectorL2OfVecField hq) -
        hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ k
          (toHilbertVectorL2OfVecField hp)))
  have hsb := MeasureTheory.Lp.coeFn_sub
    (hilbertVectorL2ToVectorL2 (toHilbertVectorL2OfVecField hq))
    (hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ k
      (toHilbertVectorL2OfVecField hp)))
  rw [hmap]
  filter_upwards [hsm, hsb, hqPlain, hWPlain, hpPlain] with x h1 h2 h3 h4 h5
  have hfl : (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k) Z x).2 =
      (ν / σ)⁻¹ • ((Z x).2 - (responseCoefficientExtension k x / σ) •
        matVecMul responsePlanarJ (Z x).1) :=
    fw_flux_snd (ν / σ) (responseCoefficientExtension k x / σ) hα (Z x).1 (Z x).2
  rw [hfl]
  change (⇑((ν / σ)⁻¹ • _ : Lp (Vec 2) 2 (volumeMeasureOn U)) x) = _
  rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, h5]

theorem fw_pair_ident (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (u : H10Function (openCubeSet Q))
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k (fun x => u.toH1Function.grad x) Z) :
    (hilbertVectorL2ToVectorL2 ((fwPairSolution Q ν σ hν hσ k u).ofLp.2 :
        HilbertVectorL2 (openCubeSet Q)) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (Z x).1) ∧
    (hilbertVectorL2ToVectorL2 (fwPairSolution Q ν σ hν hσ k u).ofLp.1 =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ k) Z x).2) := by
  let U := openCubeSet Q
  have hZ1 := hZ.1
  have hp : MemVectorL2 U (fun x => (Z x).1) := memVectorL2_fst_of_memBlockL2 hZ1.1
  have hq : MemVectorL2 U (fun x => (Z x).2) := memVectorL2_snd_of_memBlockL2 hZ1.1
  have hα : 0 < ν / σ := div_pos hν hσ
  have hmax := fw_hmax Q ν σ hσ k u Z hZ hp hq
  have hE := fw_euler (physicalSolenoidalSpace Q).toSubmodule
    (physicalPotentialSpace Q).toSubmodule (physicalPositiveShear Q σ hσ k)
    (physicalProjectedCoefficient Q σ hσ k) (fw_projCoeff_apply Q σ hσ k) (ν / σ) hα
    (fwLoad Q u) (fwX0 Q hp hZ1.2.1) (fwS0 Q hq hZ1.2.2) hmax
  obtain ⟨hyfl, hsys1, hsys2⟩ := hE
  have hz := fw_inverse_of_operator (ν / σ) hα (physicalProjectedCoefficient Q σ hσ k) _ _
    (fw_block_apply (ν / σ) (physicalProjectedCoefficient Q σ hσ k) _ _ _ hsys1 hsys2)
  have hz' : fwPairSolution Q ν σ hν hσ k u = WithLp.toLp 2 ((ν / σ)⁻¹ •
      ((fwS0 Q hq hZ1.2.2 : HilbertVectorL2 U) -
        physicalPositiveShear Q σ hσ k (fwX0 Q hp hZ1.2.1 : HilbertVectorL2 U)),
      fwX0 Q hp hZ1.2.1) := hz
  refine ⟨?_, ?_⟩
  · have e : ((fwPairSolution Q ν σ hν hσ k u).ofLp.2 : HilbertVectorL2 U) =
        toHilbertVectorL2OfVecField hp := congrArg (fun z => (z.ofLp.2 : HilbertVectorL2 U)) hz'
    rw [e, hilbertVectorL2ToVectorL2_toHilbertVectorL2 hp]
    exact coeFn_toVectorL2 hp
  · have e : (fwPairSolution Q ν σ hν hσ k u).ofLp.1 = (ν / σ)⁻¹ •
        (toHilbertVectorL2OfVecField hq -
          physicalPositiveShear Q σ hσ k (toHilbertVectorL2OfVecField hp)) :=
      congrArg (fun z => z.ofLp.1) hz'
    rw [e]
    exact fw_flux_ae Q ν σ hν hσ k Z hp hq

end

end ASDExplicitGamma.Scalar
