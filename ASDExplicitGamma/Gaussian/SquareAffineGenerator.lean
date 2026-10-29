module

public import ASDExplicitGamma.Gaussian.SquareFeedback
public import ASDExplicitGamma.Gaussian.FiniteGenerator
public import ASDExplicitGamma.Gaussian.SquareDirections
public import ASDExplicitGamma.Gaussian.SquareBudget
public import ASDExplicitGamma.Inverse.PureFluxGeneratorHistory

/-! The physical uncentered covariance generator for every affine load. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Model ASDExplicitGamma.Numerics
open scoped BigOperators
noncomputable section

local instance squareAffineGeneratorFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Actual full-shell generator with an explicit bound on the complete
inverse histories of the aligned source cells. -/
theorem square_affine_load_generator_of_history_bound
    (Q : TriadicCube 2) (m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : diagMeshRadius Q m/L.1 ≤ 1/243)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    (1/2:ℝ)*modelCovarianceTrace
      (responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P)
      (squareQ3Directions Q b L) k ≤
      19*(b^2/σ^2)*B^2*
        responseFrameEnergyObservable (measurableSet_openCubeSet Q)
          (square_volume_pos Q) ν σ hν hσ P k := by
  let hv := square_volume_pos Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv ν σ hν hσ P
  let c := |σ⁻¹| * |b|
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let H := fun l : whiteBasisIndex => squareQ3Directions Q b L (enc l)
  let Y := fun l => pureFluxResponseGeneratorY (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let Z := fun l => pureFluxResponseGeneratorZ (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q) hv ν σ hν hσ k P
  let C := fun l => inner ℝ S (responseFrameEnergyShearFamily
    (measurableSet_openCubeSet Q) hv ν σ hν hσ k (H l) (Y l))
  let g := fun l => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  obtain ⟨r, u, w, hrep, hgrad, hEv, hEu⟩ := square_minimizer_pair Q hEll P
  rw [lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hv ν σ hν hσ k] at hrep hEv hEu
  have hE : E k = 2*(responseFrameMuOperatorSystemData hU.isOpen.measurableSet hv ν σ hν hσ k).toMuHilbertRealization.muCandidate P :=
    lemmaV_observable_eq_twice_muCandidate hU.isOpen.measurableSet hv ν σ hν hσ P k
  rw [← hE] at hEv hEu
  let v := lemmaVAffinePotential hU P.1 r
  let G := fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)
  let x := Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  let y := Real.sqrt (lemmaVTiledWeakEnergy Q m G)
  have hx : x^2 = lemmaVTiledWeakEnergy Q m v.grad := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m _)
  have hy : y^2 = lemmaVTiledWeakEnergy Q m G := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m _)
  have hp : x^2+y^2 ≤ B*E k := by
    rw [hx, hy]
    exact square_minimizer_pair_tiled_energy_bound Q m ν σ hν hσ k P r u w hgrad hEv hEu B hhist
  have htrace := square_q3_generator_covariance_source_bound
    Q m ν σ b hν hσ L k P r u w hrep hgrad B hB hhist
  have hfinite (s : Finset whiteBasisIndex) :
      (1/2:ℝ)*(∑ l ∈ s, g l) ≤ 19*c^2*B^2*E k := by
    have hidentity : (1/2:ℝ)*(∑ l ∈ s, g l) =
        (∑ l ∈ s, ‖Y l‖^2)+2*(∑ l ∈ s, C l)-(∑ l ∈ s, ‖Z l‖^2) := by
      rw [Finset.mul_sum]
      simp_rw [g, pureFluxResponseHessianDiagonal_source_identity]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    have hs : (∑ l ∈ s, ‖Y l‖^2) ≤ B*c^2*(generatorKA (diagMeshRadius Q m/L.1))^2*x^2 := by
      calc
        _ ≤ ∑' l, ‖Y l‖^2 := htrace.1.sum_le_tsum s (fun _ _ => sq_nonneg _)
        _ ≤ B*(|σ⁻¹| * |b| *generatorKA (diagMeshRadius Q m/L.1))^2*lemmaVTiledWeakEnergy Q m v.grad := htrace.2
        _ = _ := by rw [hx]; dsimp only [c]; ring
    have hc : (∑ l ∈ s, C l) ≤ (63/50:ℝ)*B*c^2*generatorKA (diagMeshRadius Q m/L.1)*
        generatorKB (diagMeshRadius Q m/L.1)*x*y := by
      have hc0 := square_q3_cross_feedback_finite
        Q m ν σ b hν hσ L s k P r u w hrep hgrad B hB hhist
      have hGgrad : (((1/2:ℝ) • (w.toH1-u.toH1)) : H1Function (openCubeSet Q)).grad = G := by
        funext z j
        simp only [G, H1Function.smul_grad, H1Function.sub_grad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      dsimp only at hc0
      rw [hGgrad] at hc0
      apply (le_abs_self _).trans
      exact hc0
    rw [hidentity]
    exact source_feedback_generator_le (diagMeshRadius Q m/L.1) c B _ _ _ x y (E k)
      (div_nonneg (diagMeshRadius_pos Q m).le L.2.le) hρ hB
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) hs hc hp
  have hEd : ContDiff ℝ 2 E := responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ P
  have hdirs := squareQ3Directions_summable Q b L
  have hsecond (j : ℕ) : secondDirectionalDerivative E k
      (squareQ3Directions Q b L j) =
      pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k
        (squareQ3Directions Q b L j) := by
    unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
    exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k _ _
  have hs0 := pureFlux_secondDirectionalDerivative_summable E hEd
    (squareQ3Directions Q b L) hdirs k
  have hs1 : Summable (fun j => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
      hv ν σ hν hσ P k (squareQ3Directions Q b L j)) := by
    simpa only [hsecond] using hs0
  have hgs : Summable g := hs1.comp_injective
    (@Encodable.encode_injective whiteBasisIndex (Encodable.ofCountable whiteBasisIndex))
  have ht := pureFlux_tsum_half_le_of_finite_bounds g hgs _ hfinite
  have hz : pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k 0 = 0 := by
    have h0 : secondDirectionalDerivative E k 0 =
        pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k 0 := by
      unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
      exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k 0 0
    rw [← h0]
    simp [secondDirectionalDerivative]
  have heq : modelCovarianceTrace E (squareQ3Directions Q b L) k = ∑' l, g l := by
    rw [responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum]
    exact squareQ3Directions_tsum_apply Q b L
      (pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k) hz
  have hc2 : c^2 = b^2/σ^2 := by
    dsimp only [c]
    rw [mul_pow, sq_abs, sq_abs, inv_pow]
    ring
  rw [← heq, hc2] at ht
  exact ht


/-- Actual full-shell generator with the complete source-history maximum. -/
theorem square_affine_load_generator
    (Q : TriadicCube 2) (m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : diagMeshRadius Q m/L.1 ≤ 1/243)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
      let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ P
    (1/2:ℝ)*modelCovarianceTrace E (squareQ3Directions Q b L) k ≤
      19*(b^2/σ^2)*B^2*E k := by
  intro B E
  exact square_affine_load_generator_of_history_bound Q m ν σ b hν hσ L hρ k P B
    (pureFlux_source_tile_history_nonneg Q m _)
    (pureFlux_source_tile_history_member_le Q m _)

end
end ASDExplicitGamma.Gaussian
