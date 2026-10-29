module

public import ASDExplicitGamma.Scalar.PairedTwoSlotPointwise
public import ASDExplicitGamma.Scalar.PairedTwoSlotJoint

/-! Function-level data of the two-slot solution and its block state. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational

noncomputable section

/-- The pointwise shear `(κ/σ) J v`. -/
def shear' {U : Set (Vec 2)} (σ : ℝ) (k : ResponseCoefficient U) (z : Vec 2) (v : Vec 2) :
    Vec 2 := (responseCoefficientExtension k z / σ) • matVecMul responsePlanarJ v

theorem vecDot_J_skew (u v : Vec 2) :
    vecDot (matVecMul responsePlanarJ u) v + vecDot u (matVecMul responsePlanarJ v) = 0 := by
  simp [vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two]

/-- The block state `(x, α y + C x)` of a two-slot solution `(y, x)`. -/
def twoSlotState {U : Set (Vec 2)} (ν σ : ℝ) (k : ResponseCoefficient U)
    (xf yf : Vec 2 → Vec 2) : BlockState 2 where
  potential := xf
  flux := fun z => (ν / σ) • yf z + shear' σ k z (xf z)

theorem twoSlot_lower {U : Set (Vec 2)} {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (xf yf : Vec 2 → Vec 2) (z : Vec 2) :
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) z)
      ((twoSlotState ν σ k xf yf).eval z)).2 = yf z := by
  have hα : 0 < ν / σ := div_pos hν hσ
  change (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient (ν / σ)
    (responseCoefficientExtension k z / σ))) (xf z, (ν / σ) • yf z + shear' σ k z (xf z))).2 = _
  rw [planar_block_lower hα]
  simp only [shear', add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]

theorem twoSlot_upper {U : Set (Vec 2)} {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (xf yf : Vec 2 → Vec 2) (z : Vec 2) :
    (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) z)
      ((twoSlotState ν σ k xf yf).eval z)).1 = (ν / σ) • xf z + shear' σ k z (yf z) := by
  have hα : 0 < ν / σ := div_pos hν hσ
  change (blockMatVecMul (blockMatrixOfCoeff (responsePlanarCoefficient (ν / σ)
    (responseCoefficientExtension k z / σ))) (xf z, (ν / σ) • yf z + shear' σ k z (xf z))).1 = _
  rw [planar_block_upper hα]
  simp only [shear', add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]

theorem twoSlot_pairing {U : Set (Vec 2)} {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) (xf yf : Vec 2 → Vec 2) (z : Vec 2) :
    blockPairingIntegrand (responseFramePlanarCoefficientField ν σ k)
      (twoSlotState ν σ k xf yf) (twoSlotState ν σ k xf yf) z =
      (ν / σ) * (vecNormSq (xf z) + vecNormSq (yf z)) := by
  unfold blockPairingIntegrand blockVecDot
  rw [twoSlot_upper hν hσ, twoSlot_lower hν hσ]
  have h := vecDot_J_skew (xf z) (yf z)
  simp only [BlockState.eval, twoSlotState, shear', vecDot_add_right, vecDot_add_left,
    vecDot_smul_right, vecDot_smul_left]
  have e1 : vecDot (xf z) (xf z) = vecNormSq (xf z) := rfl
  have e2 : vecDot (yf z) (yf z) = vecNormSq (yf z) := rfl
  rw [e1, e2]
  have key : (responseCoefficientExtension k z / σ) *
      (vecDot (matVecMul responsePlanarJ (xf z)) (yf z) +
        vecDot (xf z) (matVecMul responsePlanarJ (yf z))) = 0 := by rw [h]; ring
  nlinarith [key]

end

end ASDExplicitGamma.Scalar

namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
noncomputable section

theorem vecDot_sub_left'' (a b c : Vec 2) : vecDot (a - b) c = vecDot a c - vecDot b c := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

theorem shear_eq_skew {U : Set (Vec 2)} (ν σ : ℝ) (k : ResponseCoefficient U)
    (z : Vec 2) (v : Vec 2) :
    shear' σ k z v =
      matVecMul (skewPart (responseFramePlanarCoefficientField ν σ k z)) v := by
  change _ = matVecMul (skewPart (responsePlanarCoefficient (ν / σ)
    (responseCoefficientExtension k z / σ))) v
  rw [planar_skewPart]
  ext i
  simp [shear', matVecMul, Matrix.smul_apply, mul_add, mul_assoc]

theorem shear_memL2 {Q : TriadicCube 2} {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {v : Vec 2 → Vec 2}
    (hv : MemVectorL2 (openCubeSet Q) v) :
    MemVectorL2 (openCubeSet Q) (fun z => shear' σ k z (v z)) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    ν σ hν hσ k
  have := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hv
  convert this using 1
  funext z
  exact shear_eq_skew ν σ k z (v z)

/-- The weak equation of the two-slot block state against every variation. -/
theorem two_slot_hforced {Q : TriadicCube 2} {ν σ : ℝ} (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q))
    (φ : H10Function (openCubeSet Q)) (η : H1Function (openCubeSet Q))
    {G : Vec 2 → Vec 2} (hG : MemVectorL2 (openCubeSet Q) G)
    (hd : IsSolenoidalOn (openCubeSet Q) (fun z =>
      (ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z) - G z)) :
    ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand
        (responseFramePlanarCoefficientField ν σ k) T
        (twoSlotState ν σ k φ.toH1Function.grad η.grad)) =
        volumeAverage (openCubeSet Q) (fun z => vecDot (T.potential z) (G z)) := by
  intro T hT
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hx : MemVectorL2 (openCubeSet Q) φ.toH1Function.grad := φ.toH1Function.grad_memVectorL2
  have hy : MemVectorL2 (openCubeSet Q) η.grad := η.grad_memVectorL2
  have hTp : MemVectorL2 (openCubeSet Q) T.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hT.1
  have hTf : MemVectorL2 (openCubeSet Q) T.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hT.1
  have hshy := shear_memL2 hν hσ k hy
  have hU : MemVectorL2 (openCubeSet Q) (fun z =>
      (ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z)) :=
    (hx.const_smul (ν / σ)).add hshy
  have hpoint : ∀ z, blockPairingIntegrand (responseFramePlanarCoefficientField ν σ k) T
      (twoSlotState ν σ k φ.toH1Function.grad η.grad) z =
      vecDot (T.potential z) ((ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z)) +
        vecDot (T.flux z) (η.grad z) := by
    intro z
    unfold blockPairingIntegrand blockVecDot
    rw [twoSlot_upper hν hσ, twoSlot_lower hν hσ]
    rfl
  obtain ⟨ψ, hψ⟩ := hT.2.1
  have h1 : ∫ z in openCubeSet Q, vecDot (T.potential z)
      ((ν / σ) • φ.toH1Function.grad z + shear' σ k z (η.grad z)) ∂volume =
      ∫ z in openCubeSet Q, vecDot (T.potential z) (G z) ∂volume := by
    have h0 : ∫ z in openCubeSet Q, vecDot (((ν / σ) • φ.toH1Function.grad z +
        shear' σ k z (η.grad z)) - G z) (T.potential z) ∂volume = 0 := by
      have h00 := hd ψ
      simp only [hψ] at h00
      exact h00
    have hint1 := integrableOn_vecDot_of_memVectorL2 hTp hU
    have hint2 := integrableOn_vecDot_of_memVectorL2 hTp hG
    have e : (fun z => vecDot (((ν / σ) • φ.toH1Function.grad z +
          shear' σ k z (η.grad z)) - G z) (T.potential z)) =
        fun z => vecDot (T.potential z) ((ν / σ) • φ.toH1Function.grad z +
          shear' σ k z (η.grad z)) - vecDot (T.potential z) (G z) := by
      funext z
      rw [vecDot_sub_left'', vecDot_comm, vecDot_comm (G z)]
    rw [e, integral_sub hint1 hint2] at h0
    linarith
  have h2 : ∫ z in openCubeSet Q, vecDot (T.flux z) (η.grad z) ∂volume = 0 := hT.2.2 η
  have hint1 := integrableOn_vecDot_of_memVectorL2 hTp hU
  have hint3 := integrableOn_vecDot_of_memVectorL2 hTf hy
  unfold volumeAverage
  congr 1
  simp only [hpoint]
  rw [integral_add hint1 hint3, h1, h2, add_zero]

end
end ASDExplicitGamma.Scalar
