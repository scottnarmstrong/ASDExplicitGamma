module

public import ASDExplicitGamma.Native.ParentBoundaryInverseGenerator
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankAdapter

/-! Sharp inverse lower generator on the actual closed-cube test. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Exact canonical q3 bank generator at an arbitrary continuous base coefficient. -/
theorem parent_boundary_inverse_bank_generator (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet (originCube 2 n)), ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) (pureFluxBankSourceDepth s),
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n f))
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    (1/2:ℝ)*modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ)
      (pureFluxMainCubeQ3Directions n b (q3ModelLength (n+(s:ℤ)))) f ≥
      -(b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceB 0 (s-1)) (pureFluxCovarianceA 0 (s-1))*B^2*
        bankInverseTraceObservable n ν σ hν hσ f) := by
  let Q := originCube 2 n
  let L := q3ModelLength (n+(s:ℤ))
  let H := pureFluxMainCubeQ3Directions n b L
  let center := pureFluxParentCenter n
  let Hc := fun j => pureFluxCoefficientCentering center (H j)
  let k := pureFluxOpenResponseRestriction n f
  let E := pureFluxBankLoadEnergy n ν σ hν hσ
  have hH : Summable (fun j => ‖H j‖^2) :=
    @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet Q), ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hHc : Summable (fun j => ‖Hc j‖^2) :=
    summable_sq_bounded_image H hH (pureFluxCoefficientCentering center)
  have hdirs : (fun j => pureFluxOpenResponseRestriction n (Hc j)) =
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L := by
    funext j
    exact (pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction n b L j).symm
  have htrace : modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ) H f =
      ∑ i : Fin 2, modelCovarianceTrace (E i)
        (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k := by
    calc
      _ = modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ) Hc f := by
        simpa only [Hc, pureFluxCoefficientCentering_apply] using
          (pureFlux_bank_covarianceTrace_centered n ν σ hν hσ H f center).symm
      _ = _ := by
        rw [pureFlux_bank_covarianceTrace_eq_open_load_sum n ν σ hν hσ Hc hHc f, hdirs]
  have hbound (i : Fin 2) := parent_boundary_affine_inverse_generator_lower n 0 (s-1)
    (pureFluxBankSourceDepth s) ν σ b B hν hσ L (pureFlux_bank_source_rho n s hs)
    (pureFlux_bank_source_delta n s hs) k (0,Pi.single i 1) hB hhist
  rw [htrace,Finset.mul_sum]
  calc
    _ ≥ ∑ i : Fin 2,-(b^2/σ^2*pureFluxCovarianceMu
        (pureFluxCovarianceB 0 (s-1)) (pureFluxCovarianceA 0 (s-1))*B^2*E i k) :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by
      rw [Finset.sum_neg_distrib,←Finset.mul_sum,pureFlux_bank_observable_eq_open_load_sum]

end
end ASDExplicitGamma.Native
