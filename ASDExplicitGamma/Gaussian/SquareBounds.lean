module

public import ASDExplicitGamma.Gaussian.SquareAffineGenerator
public import ASDExplicitGamma.Gaussian.SquareBracket

/-! The pathwise generator and bracket for the actual physical q3 shell. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- The physical trace Hessian is the sum of its four physical load Hessians
on the same translated square. -/
theorem squareTrace_secondDirectional_eq_load_sum
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k H : ResponseCoefficient (openCubeSet Q)) :
    secondDirectionalDerivative (squareTrace Q ν σ) k H =
      ∑ p : Fin 2 × Bool,
        secondDirectionalDerivative (squareLoadEnergy Q ν σ hν hσ p) k H := by
  have hEq : (fun z => fderiv ℝ (squareTrace Q ν σ) z H) =
      fun z => ∑ p : Fin 2 × Bool, fderiv ℝ (squareLoadEnergy Q ν σ hν hσ p) z H := by
    funext z
    exact squareTrace_fderiv_eq_load_sum Q ν σ hν hσ z H
  have hD (p : Fin 2 × Bool) : DifferentiableAt ℝ
      (fun z => fderiv ℝ (squareLoadEnergy Q ν σ hν hσ p) z H) k := by
    have hC2 : ContDiff ℝ 2 (squareLoadEnergy Q ν σ hν hσ p) :=
      responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ _
    have hFd : ContDiffAt ℝ 1 (fderiv ℝ (squareLoadEnergy Q ν σ hν hσ p)) k :=
      hC2.contDiffAt.fderiv_right (by norm_num)
    exact (hFd.clm_apply contDiffAt_const).differentiableAt (by norm_num)
  have hfun : (fun z => ∑ p : Fin 2 × Bool,
      fderiv ℝ (squareLoadEnergy Q ν σ hν hσ p) z H) =
      ∑ p : Fin 2 × Bool, fun z => fderiv ℝ (squareLoadEnergy Q ν σ hν hσ p) z H := by
    funext z
    simp
  unfold secondDirectionalDerivative
  rw [hEq, hfun]
  exact congrArg (fun D : ResponseCoefficient (openCubeSet Q) →L[ℝ] ℝ => D H)
    (fderiv_sum (fun p _ => hD p))

/-- The full-shell covariance contraction of the actual trace is the sum
of the four physical affine-load contractions. -/
theorem square_trace_covariance_eq_load_sum
    (Q : TriadicCube 2) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet Q)) :
    modelCovarianceTrace (squareTrace Q ν σ)
        (squareQ3Directions Q b L) k =
      ∑ p : Fin 2 × Bool, modelCovarianceTrace (squareLoadEnergy Q ν σ hν hσ p)
        (squareQ3Directions Q b L) k := by
  let H := squareQ3Directions Q b L
  have hH := squareQ3Directions_summable Q b L
  have hE (p : Fin 2 × Bool) : ContDiff ℝ 2 (squareLoadEnergy Q ν σ hν hσ p) :=
    responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ _
  have hs (p : Fin 2 × Bool) : Summable (fun n =>
      secondDirectionalDerivative (squareLoadEnergy Q ν σ hν hσ p) k (H n)) :=
    pureFlux_secondDirectionalDerivative_summable _ (hE p) H hH k
  calc
    _ = ∑' n, ∑ p : Fin 2 × Bool,
        secondDirectionalDerivative (squareLoadEnergy Q ν σ hν hσ p) k (H n) := by
      apply tsum_congr
      intro n
      exact squareTrace_secondDirectional_eq_load_sum Q ν σ hν hσ k (H n)
    _ = ∑ p : Fin 2 × Bool, ∑' n,
        secondDirectionalDerivative (squareLoadEnergy Q ν σ hν hσ p) k (H n) :=
      Summable.tsum_finsetSum (fun p _ => hs p)
    _ = _ := rfl

/-- The generator and bracket bounds on an arbitrary translated square: the actual full-shell drift and
bracket, in the fixed deterministic frame, with the complete source history. -/
theorem square_shell_generator_bracket
    (Q : TriadicCube 2) (j : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hratio : diagMeshRadius Q j / L.1 ≤ 1 / 243)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let T := squareTrace Q ν σ k
    let B := pureFluxSourceTileHistory Q j (responseFramePlanarCoefficientField ν σ k)
    let H := squareQ3Directions Q b L
    (1 / 2 : ℝ) * modelCovarianceTrace (squareTrace Q ν σ) H k ≤
      19 * (b ^ 2 / σ ^ 2) * B ^ 2 * (T + 4) ∧
    Summable (fun n => (fderiv ℝ (squareTrace Q ν σ) k (H n)) ^ 2) ∧
    (∑' n, (fderiv ℝ (squareTrace Q ν σ) k (H n)) ^ 2) ≤
      16 * (b ^ 2 / σ ^ 2) * B ^ 2 * T * (T + 4) := by
  let B := pureFluxSourceTileHistory Q j (responseFramePlanarCoefficientField ν σ k)
  let H := squareQ3Directions Q b L
  let E := squareLoadEnergy Q ν σ hν hσ
  have hload (p : Fin 2 × Bool) :
      (1 / 2 : ℝ) * modelCovarianceTrace (E p) H k ≤
        19 * (b ^ 2 / σ ^ 2) * B ^ 2 * E p k := by
    exact square_affine_load_generator Q j ν σ b hν hσ L hratio k
      (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hload p)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hfull : (∑ p : Fin 2 × Bool, E p k) = squareTrace Q ν σ k + 4 := by
    have he := squareTrace_eq_load_sum Q ν σ hν hσ k
    dsimp only [E]
    linarith only [he]
  rw [hfull] at hsum
  refine ⟨?_, square_shell_bracket Q j ν σ b hν hσ L hratio k⟩
  rw [square_trace_covariance_eq_load_sum Q ν σ b hν hσ L k]
  simpa only [E, H, B] using hsum

end
end ASDExplicitGamma.Gaussian
