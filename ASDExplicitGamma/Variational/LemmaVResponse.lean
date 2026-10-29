module

public import ASDExplicitGamma.Variational.LemmaVMinimizer

/-! Correlated load defects and their physical first variations. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response

noncomputable section

private theorem lemmaV_halfPair_potential {U : Set (Vec 2)} (a : CoeffField 2)
    (u : AHarmonicFunction a U) (v : AHarmonicFunction (adjointCoeffField a) U) (x : Vec 2) :
    (blockResponsePairHalfState a u v).potential x =
      (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := by
  change (((1 / 2 : ℝ) • blockResponsePairState a u v).eval x).1 = _
  rw [BlockState.eval_smul]
  rfl

/-- For every physical load, choose harmonic witnesses once, before the
perturbation direction. The chosen affine potential and both defect energy
identities are correlated with both first-variation signs. -/
theorem lemmaV_response_load_pair (m : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (P : BlockVec 2) :
    let U := openCubeSet (originCube 2 m)
    let hU := isOpenBoundedConvexDomain_openCubeSet (originCube 2 m)
    let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) m
    let a := responseFramePlanarCoefficientField ν σ k
    let E := responseFrameEnergyObservable hU.isOpen.measurableSet hv ν σ hν hσ P
    ∃ r : H10Function U, ∃ u : AHarmonicFunction a U,
      ∃ v : AHarmonicFunction (adjointCoeffField a) U,
        ((lemmaVAffinePotential hU P.1 r).grad =ᵐ[volumeMeasureOn U]
          fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2) ∧
        (E k - 2 * vecDot P.1 P.2 =
          volumeAverage U (scalarVariationEnergyIntegrand (adjointCoeffField a) v)) ∧
        (E k + 2 * vecDot P.1 P.2 =
          volumeAverage U (scalarVariationEnergyIntegrand a u)) ∧
        (∀ H : ResponseCoefficient U,
          (fderiv ℝ E k H = 2 * volumeAverage U (fun x =>
            (responseCoefficientExtension H x / σ) * vecDot (v.toH1.grad x)
              (matVecMul responsePlanarJ ((lemmaVAffinePotential hU P.1 r).grad x)))) ∧
          (fderiv ℝ E k H = 2 * volumeAverage U (fun x =>
            -(responseCoefficientExtension H x / σ) * vecDot (u.toH1.grad x)
              (matVecMul responsePlanarJ ((lemmaVAffinePotential hU P.1 r).grad x))))) := by
  intro U hU hv a E
  have hEll := responseFramePlanarCoefficientField_isElliptic hU.isOpen.measurableSet
    ν σ hν hσ k
  let M := responseFrameMuOperatorSystemData hU.isOpen.measurableSet hv ν σ hν hσ k
  obtain ⟨r, u, v, hrep, hpot, hEv, hEu⟩ := lemmaV_minimizer_pair m hEll P
  rw [lemmaV_responseSystem_eq_canonical] at hrep hEv hEu
  let V := lemmaVAffinePotential hU P.1 r
  have hmid : V.grad =ᵐ[volumeMeasureOn U]
      fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2 := by
    filter_upwards [hpot] with x hx
    rw [hx, lemmaV_halfPair_potential]
    ext i
    change (1 / 2 : ℝ) * (u.toH1.grad x i + v.toH1.grad x i) = _
    ring
  have hE : E k = 2 * M.toMuHilbertRealization.muCandidate P := by
    exact lemmaV_observable_eq_twice_muCandidate hU.isOpen.measurableSet hv ν σ hν hσ P k
  refine ⟨r, u, v, hmid, ?_, ?_, ?_⟩
  · rw [hE]
    exact hEv
  · rw [hE]
    exact hEu
  · intro H
    have hlower := blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
      a hEll u v
    have hcore : fderiv ℝ E k H = 2 * volumeAverage U (fun x =>
        -(responseCoefficientExtension H x / σ) *
          vecDot ((1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x))
            (matVecMul responsePlanarJ (V.grad x))) := by
      rw [lemmaV_load_first_variation]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hrep, hpot, hlower] with x hx hp hl
      have hfirst : (hilbertBlockL2ToBlockL2
          (M.toMuHilbertRealization.minimizerMap P) x).1 = V.grad x := by
        exact (congrArg Prod.fst hx).trans hp.symm
      have hconj : lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 (M.toMuHilbertRealization.minimizerMap P) x) =
            (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x) := by
        rw [← lemmaV_planar_lower_image ν σ _ hν hσ, hx]
        exact hl
      rw [hconj, hfirst]
    constructor
    · rw [hcore]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hmid] with x hx
      have hp : V.grad x = (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := by
        rw [hx]
        ext i
        simp [div_eq_mul_inv, mul_comm]
      rw [hp]
      exact lemmaV_halfPair_envelope_plus _ _ _
    · rw [hcore]
      congr 1
      unfold volumeAverage
      congr 1
      apply integral_congr_ae
      filter_upwards [hmid] with x hx
      have hp : V.grad x = (1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x) := by
        rw [hx]
        ext i
        simp [div_eq_mul_inv, mul_comm]
      rw [hp]
      exact lemmaV_halfPair_envelope_minus _ _ _

end

end ASDExplicitGamma.Variational
