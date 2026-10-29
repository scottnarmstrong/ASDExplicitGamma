module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorPairedEnergy
public import ASDExplicitGamma.Variational.LemmaVHaar
public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy

/-! Exact weak and energy identifications for the actual affine minimizer pair. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

theorem pureFlux_tiledWeakEnergy_h1_congr (Q : TriadicCube 2) (m : ℕ)
    (u v : H1Function (openCubeSet Q))
    (h : u.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] v.grad) :
    lemmaVTiledWeakEnergy Q m u.grad = lemmaVTiledWeakEnergy Q m v.grad := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3:ℝ)]
  dsimp only [lemmaVTiledWeakEnergy, descendantsAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply lemmaV_dualEnergy_congr_ae R hq
    (memLp_on_descendant_of_memLp hR (u.grad_memL2_normalizedCubeMeasure i))
    (memLp_on_descendant_of_memLp hR (v.grad_memL2_normalizedCubeMeasure i))
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact (ae_restrict_of_ae_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hR) h).mono
    fun x hx => congrFun hx i

theorem pureFlux_tiledWeakEnergy_h1_neg (Q : TriadicCube 2) (m : ℕ)
    (v : H1Function (openCubeSet Q)) :
    lemmaVTiledWeakEnergy Q m (fun x => -v.grad x) = lemmaVTiledWeakEnergy Q m v.grad := by
  dsimp only [lemmaVTiledWeakEnergy, descendantsAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  have hs := sensitivity_vectorWeakEnergy_smul R v.grad
    (fun i => memLp_on_descendant_of_memLp hR (v.grad_memL2_normalizedCubeMeasure i)) (-1)
  have hf : (fun x => -v.grad x) = fun x i => (-1:ℝ)*v.grad x i := by
    funext x i
    simp only [Pi.neg_apply, neg_one_mul]
  rw [hf]
  simpa only [neg_one_sq, one_mul] using hs

theorem pureFlux_minimizer_pair_tiled_energy_bound (n : ℤ) (m : ℕ)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (r : H10Function (openCubeSet (originCube 2 n)))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k) (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hgrad : (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) P.1 r).grad =ᵐ[
      volumeMeasureOn (openCubeSet (originCube 2 n))]
      (blockResponsePairHalfState (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (hEv : responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k - 2*vecDot P.1 P.2 =
      volumeAverage (openCubeSet (originCube 2 n))
        (scalarVariationEnergyIntegrand (adjointCoeffField (responseFramePlanarCoefficientField ν σ k)) w))
    (hEu : responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k + 2*vecDot P.1 P.2 =
      volumeAverage (openCubeSet (originCube 2 n))
        (scalarVariationEnergyIntegrand (responseFramePlanarCoefficientField ν σ k) u))
    (B : ℝ) (hhist : ∀ R ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory R (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    lemmaVTiledWeakEnergy (originCube 2 n) m
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) P.1 r).grad +
      lemmaVTiledWeakEnergy (originCube 2 n) m (fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)) ≤
      B * responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k := by
  let Q := originCube 2 n
  let a := responseFramePlanarCoefficientField ν σ k
  let V := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
  let f : H1Function (openCubeSet Q) := (1/2:ℝ) • (u.toH1+w.toH1)
  let g : H1Function (openCubeSet Q) := (1/2:ℝ) • (u.toH1-w.toH1)
  have hfirst : f.grad = compatiblePairFirst u w := by rfl
  have hsecond : g.grad = compatiblePairSecondImage u w := by
    funext x i
    simp only [g, compatiblePairSecondImage, H1Function.smul_grad, H1Function.sub_grad,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hV : V.grad =ᵐ[volumeMeasureOn (openCubeSet Q)] f.grad := hgrad
  have hneg : (fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)) = fun x => -g.grad x := by
    funext x i
    simp only [g, H1Function.smul_grad, H1Function.sub_grad, Pi.smul_apply, Pi.sub_apply,
      Pi.neg_apply, smul_eq_mul]
    ring
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hp := pureFlux_paired_tiled_energy_bound Q m hEll u w B hhist
  have hE := compatiblePairState_energy Q hEll u w
  have heq : blockPairingAverage (openCubeSet Q) a (compatiblePairState u w) (compatiblePairState u w) =
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k := by
    rw [hE]
    linarith only [hEv, hEu]
  rw [heq] at hp
  rw [← hfirst, ← hsecond] at hp
  rw [pureFlux_tiledWeakEnergy_h1_congr Q m V f hV, hneg, pureFlux_tiledWeakEnergy_h1_neg]
  exact hp

end
end ASDExplicitGamma.Inverse
