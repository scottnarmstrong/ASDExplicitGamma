module

public import ASDExplicitGamma.Scalar.DropScaledCopies

/-! Homogeneity of the four-term resolvent observables in the insertion. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace Topology ENNReal

noncomputable section

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem drop_g1Hessian_smul (B J : H →L[ℝ] H) (f : H) (C : H →L[ℝ] H) (s : ℝ) :
    hilbertG1HessianTerm B J f (s • C) = s ^ 2 * hilbertG1HessianTerm B J f C := by
  simp [hilbertG1HessianTerm, inner_smul_right]
  ring

end Hilbert

section Physical

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem drop_fluxBlock_smul (s : ℝ) (D : X →L[ℝ] Y) :
    pureFluxBlockOperator 0 (s • D) = s • pureFluxBlockOperator 0 D := by
  ext z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ Y X).injective
  change (pureFluxBlockOperator 0 (s • D) z).ofLp = (s • pureFluxBlockOperator 0 D z).ofLp
  rw [pureFluxBlockOperator_apply]
  ext <;> simp [ContinuousLinearMap.smul_apply]

end Physical

theorem drop_projCoeff_smul (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ) (s : ℝ)
    (H : ResponseCoefficient (openCubeSet Q)) :
    physicalProjectedCoefficient Q σ hσ (s • H) = s • physicalProjectedCoefficient Q σ hσ H := by
  have hS := responseShearL2Operator_smul (measurableSet_openCubeSet Q) σ hσ s H
  unfold physicalProjectedCoefficient physicalPositiveShear
  rw [hS]
  ext x
  simp [ContinuousLinearMap.smul_apply]

theorem drop_coefficient_smul {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2) (σ : ℝ)
    (hσ : 0 < σ) (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (s : ℝ) (y : C(K, ℝ)) :
    physicalParityCoefficient Q σ hσ R (s • y) = s • physicalParityCoefficient Q σ hσ R y := by
  unfold physicalParityCoefficient
  rw [map_smul, drop_projCoeff_smul]

theorem drop_hessian_smul {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (e : Vec 2) (s : ℝ) (x y : C(K, ℝ)) :
    physicalParityHessianObservable Q ν σ hν hσ R e (x, s • y) =
      s ^ 2 * physicalParityHessianObservable Q ν σ hν hσ R e (x, y) := by
  unfold physicalParityHessianObservable
  simp only [drop_coefficient_smul, drop_fluxBlock_smul]
  exact drop_g1Hessian_smul _ _ _ _ s

end

end ASDExplicitGamma.Scalar
