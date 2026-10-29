module

public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorBound
public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorFeedback
public import ASDExplicitGamma.Native.ParentBoundaryCommonGeneratorCoefficient
public import ASDExplicitGamma.Gaussian.SquareBudget

/-! Actual finite covariance generators with a common original spatial center. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped BigOperators
noncomputable section

local instance parentCommonFiniteGeneratorMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Full actual affine-load covariance generator, retaining the original
common center and every source-minus-projection term. All minimizer witnesses
are constructed internally; the only inputs are physical coefficient links
and the literal histories of the actual coefficient. -/
theorem parent_boundary_common_finite_affine_generator
    (P0 Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P0)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (P : BlockVec 2) (k : ResponseCoefficient (openCubeSet Q))
    (H : whiteBasisIndex → ResponseCoefficient (openCubeSet Q))
    (hlink : ∀ l,(parentBoundaryCommonBasisMultiplier P0 Q b σ L l).toFun =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseCoefficientExtension (H l) x / σ)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth Q m,lemmaVInverseHistory U
      (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B)
    (s : Finset whiteBasisIndex) :
    (1/2:ℝ)*(∑ l ∈ s,pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
      (square_volume_pos Q) ν σ hν hσ P k (H l)) ≤
    |σ⁻¹|^2*pureFluxCovarianceMu (parentBoundaryCommonRowCoefficient P0 Q b L m)
      (parentBoundaryCommonFeedbackCoefficient P0 Q b L m)*B^2*
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (square_volume_pos Q) ν σ hν hσ P k := by
  let hv := square_volume_pos Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv ν σ hν hσ P
  let A := parentBoundaryCommonRowCoefficient P0 Q b L m
  let D := parentBoundaryCommonFeedbackCoefficient P0 Q b L m
  let c := |σ⁻¹|
  let Y := fun l => pureFluxResponseGeneratorY (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let Z := fun l => pureFluxResponseGeneratorZ (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q) hv ν σ hν hσ k P
  let C := fun l => inner ℝ S (responseFrameEnergyShearFamily
    (measurableSet_openCubeSet Q) hv ν σ hν hσ k (H l) (Y l))
  let g := fun l => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  obtain ⟨r,u,w,hrep,hgrad,hEv,hEu⟩ := square_minimizer_pair Q hEll P
  rw [lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hv ν σ hν hσ k] at hrep hEv hEu
  have hE : E k = 2*(responseFrameMuOperatorSystemData hU.isOpen.measurableSet hv ν σ hν hσ k).toMuHilbertRealization.muCandidate P :=
    lemmaV_observable_eq_twice_muCandidate hU.isOpen.measurableSet hv ν σ hν hσ P k
  rw [← hE] at hEv hEu
  let v := lemmaVAffinePotential hU P.1 r
  let G := fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)
  have hbase : (fun x => (hilbertBlockL2ToBlockL2
      ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.grad := by
    filter_upwards [hrep,hgrad] with x hxrep hxgrad
    have hx := congrArg Prod.fst hxrep
    have hx' : (hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) x).1 =
        (blockResponsePairHalfState a u w).potential x := hx
    exact hx'.trans hxgrad.symm
  let x := Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  let y := Real.sqrt (lemmaVTiledWeakEnergy Q m G)
  have hx : x^2 = lemmaVTiledWeakEnergy Q m v.grad := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m _)
  have hy : y^2 = lemmaVTiledWeakEnergy Q m G := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m _)
  have hp : x^2+y^2 ≤ B*E k := by
    rw [hx,hy]
    exact square_minimizer_pair_tiled_energy_bound Q m ν σ hν hσ k P r u w hgrad hEv hEu B hhist
  have htrace := parent_boundary_common_generatorY_trace_bound
    P0 Q hQP ν σ b hν hσ L m P k H r hlink hbase B hB hhist
  have hidentity : (1/2:ℝ)*(∑ l ∈ s,g l) =
      (∑ l ∈ s,‖Y l‖^2)+2*(∑ l ∈ s,C l)-(∑ l ∈ s,‖Z l‖^2) := by
    rw [Finset.mul_sum]
    simp_rw [g,pureFluxResponseHessianDiagonal_source_identity]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
    rfl
  have hs : (∑ l ∈ s,‖Y l‖^2) ≤ B*c^2*A^2*x^2 := by
    calc
      _ ≤ ∑' l,‖Y l‖^2 := htrace.1.sum_le_tsum s (fun _ _ => sq_nonneg _)
      _ ≤ B*(|σ⁻¹| * A)^2*lemmaVTiledWeakEnergy Q m v.grad := htrace.2
      _ = _ := by rw [hx]; dsimp only [c]; ring
  have hc : (∑ l ∈ s,C l) ≤ (63/50:ℝ)*B*c^2*A*D*x*y := by
    have hc0 := parent_boundary_common_generator_cross_feedback
      P0 Q hQP ν σ b hν hσ L m s P k H r hlink hbase u w hrep B hB hhist
    have hGgrad : (((1/2:ℝ) • (w.toH1-u.toH1)) : H1Function (openCubeSet Q)).grad = G := by
      funext z j
      simp only [G,H1Function.smul_grad,H1Function.sub_grad,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
    dsimp only at hc0
    rw [hGgrad] at hc0
    exact (le_abs_self _).trans hc0
  exact parent_boundary_common_source_feedback_scalar A D c B _ _ _ _ x y (E k) hB hidentity
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) hs hc hp

end
end ASDExplicitGamma.Native
