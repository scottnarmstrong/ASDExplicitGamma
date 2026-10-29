module

public import ASDExplicitGamma.Variational.LemmaVResponse
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! Actual load potentials and their defect/response H1 estimates. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

/-- Sign of a normalized doubled load. -/
def lemmaVLoadSign (b : Bool) : ℝ := if b then 1 else -1

/-- Choose the affine potential and the defect potential for each signed
load. All H1 estimates and first-variation identities are proved here. -/
theorem lemmaV_load_bounds (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (i : Fin 2) (b : Bool) :
    let Q := originCube 2 m
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) m
    let a := responseFramePlanarCoefficientField ν σ k
    let P := orthonormalFrameLoad i (lemmaVLoadSign b)
    let E := responseFrameEnergyObservable hU.isOpen.measurableSet hv ν σ hν hσ P
    let B := lemmaVTileHistory Q j a
    ∃ r : H10Function U, ∃ w : H1Function U,
      (lemmaVTiledWeakEnergy Q j w.grad ≤ B * (E k - 1)) ∧
      (lemmaVTiledWeakEnergy Q j (lemmaVAffinePotential hU P.1 r).grad ≤ B * E k) ∧
      (0 ≤ E k - 1) ∧
      (∀ H : ResponseCoefficient U, fderiv ℝ E k H =
        2 * lemmaVLoadSign b * volumeAverage U (fun x => vecDot
          ((responseCoefficientExtension H x / σ) • matVecMul responsePlanarJ
            ((lemmaVAffinePotential hU P.1 r).grad x)) (w.grad x))) := by
  intro Q U hU hv a P E B
  have hEll := responseFramePlanarCoefficientField_isElliptic hU.isOpen.measurableSet ν σ hν hσ k
  obtain ⟨r, u, v, hmid, hEv, hEu, hderiv⟩ := lemmaV_response_load_pair m ν σ hν hσ k P
  let V := lemmaVAffinePotential hU P.1 r
  have hUweak := lemmaV_harmonic_tiledWeakEnergy_le Q j hEll u
  have hVweak := lemmaV_adjoint_tiledWeakEnergy_le Q j hEll v
  have hEu' : cubeAverage Q (scalarVariationEnergyIntegrand a u) = E k + 2 * vecDot P.1 P.2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hEu.symm
  have hEv' : cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) =
      E k - 2 * vecDot P.1 P.2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hEv.symm
  rw [hEu'] at hUweak
  rw [hEv'] at hVweak
  have hVbound : lemmaVTiledWeakEnergy Q j V.grad ≤ B * E k := by
    have h := lemmaV_tiledWeakEnergy_midpoint_le Q j V u.toH1 v.toH1 hmid
    linarith only [h, hUweak, hVweak]
  have hUenergy : 0 ≤ E k + 2 * vecDot P.1 P.2 := by
    rw [hEu]
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U a hEll u
  have hVenergy : 0 ≤ E k - 2 * vecDot P.1 P.2 := by
    rw [hEv]
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn U _
      (isEllipticFieldOn_adjointCoeffField hEll) v
  have hpair : 2 * vecDot P.1 P.2 = lemmaVLoadSign b := lemmaV_orthonormalFrameLoad_pairing i _
  rw [hpair] at hUweak hVweak hUenergy hVenergy
  cases b with
  | true =>
    refine ⟨r, v.toH1, hVweak, hVbound, hVenergy, ?_⟩
    intro H
    rw [(hderiv H).1]
    change 2 * volumeAverage U _ = 2 * 1 * volumeAverage U _
    rw [mul_one]
    congr 1
    congr 1
    funext x
    rw [vecDot_smul_left, vecDot_comm]
  | false =>
    have hUb : lemmaVTiledWeakEnergy Q j u.toH1.grad ≤ B * (E k - 1) := by
      simpa [lemmaVLoadSign, sub_eq_add_neg] using hUweak
    have hUn : 0 ≤ E k - 1 := by simpa [lemmaVLoadSign, sub_eq_add_neg] using hUenergy
    refine ⟨r, u.toH1, hUb, hVbound, hUn, ?_⟩
    intro H
    rw [(hderiv H).2]
    change 2 * volumeAverage U _ = 2 * (-1) * volumeAverage U _
    have hneg := volumeAverage_smul U (-1 : ℝ) (fun x =>
      (responseCoefficientExtension H x / σ) * vecDot (u.toH1.grad x)
        (matVecMul responsePlanarJ (V.grad x)))
    have heq : (fun x => -(responseCoefficientExtension H x / σ) *
        vecDot (u.toH1.grad x) (matVecMul responsePlanarJ (V.grad x))) =
        (-1 : ℝ) • (fun x => (responseCoefficientExtension H x / σ) *
          vecDot (u.toH1.grad x) (matVecMul responsePlanarJ (V.grad x))) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, hneg]
    have heq' : (fun x => (responseCoefficientExtension H x / σ) *
        vecDot (u.toH1.grad x) (matVecMul responsePlanarJ (V.grad x))) =
        fun x => vecDot ((responseCoefficientExtension H x / σ) •
          matVecMul responsePlanarJ (V.grad x)) (u.toH1.grad x) := by
      funext x
      rw [vecDot_smul_left, vecDot_comm]
    rw [heq']
    ring

end

end ASDExplicitGamma.Variational
