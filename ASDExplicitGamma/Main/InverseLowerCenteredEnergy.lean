module

public import ASDExplicitGamma.Main.InverseLowerCenteredProjectedQ3
public import ASDExplicitGamma.Variational.LemmaVEnvelope
public import ASDExplicitGamma.Variational.LocalizedEnergyBounds

/-! The actual response-pair gradients consume the frame energy. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

namespace ASDExplicitGamma.Main

local instance mainInverseCenteredEnergyFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

/-- The average and difference gradients of the actual response pair together
are controlled by its exact fixed-frame minimizer energy. -/
theorem main_response_pair_tiled_weighted_energy_le
    (n : ℤ) (m : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (r : H10Function (openCubeSet (originCube 2 n)))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x))
    (hgrad : (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) P.1 r).grad =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).potential) :
    let Q := originCube 2 n
    let U := openCubeSet Q
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function U := (1 / 2 : ℝ) • (w.toH1-u.toH1)
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    (ν / σ) * (lemmaVTiledWeakEnergy Q m v.grad +
      lemmaVTiledWeakEnergy Q m g.grad) ≤ ‖S‖ ^ 2 := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let a := responseFramePlanarCoefficientField ν σ k
  let M := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let X : HilbertBlockL2 U := M.toMuHilbertRealization.minimizerMap P
  let S : EnergyCarrier D := responseFrameEnergyBaseMinimizer
    (measurableSet_openCubeSet Q) hv ν σ hν hσ k P
  let v := lemmaVAffinePotential hU P.1 r
  let g : H1Function U := (1 / 2 : ℝ) • (w.toH1-u.toH1)
  have hfirst : (fun x => (hilbertBlockL2ToBlockL2 X x).1) =ᵐ[
      volumeMeasureOn U] v.grad := by
    filter_upwards [hrep, hgrad] with x hx hg
    have hrepFirst := congrArg Prod.fst hx
    have hrepFirst' : (hilbertBlockL2ToBlockL2 X x).1 =
        (blockResponsePairHalfState a u w).potential x := by
      simpa [X, M, BlockState.eval] using hrepFirst
    exact hrepFirst'.trans hg.symm
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  have hlower := blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
    a hEll u w
  have hconj : (fun x => lemmaVConjugateGradient ν σ
      (responseCoefficientExtension k x) (hilbertBlockL2ToBlockL2 X x)) =ᵐ[
        volumeMeasureOn U] fun x => -g.grad x := by
    filter_upwards [hrep, hlower] with x hx hl
    have hpair : hilbertBlockL2ToBlockL2 X x =
        (blockResponsePairHalfState a u w).eval x := hx
    have hmat := lemmaV_planar_lower_image ν σ
      (responseCoefficientExtension k x) hν hσ (hilbertBlockL2ToBlockL2 X x)
    have hmat' : (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (hilbertBlockL2ToBlockL2 X x)).2 =
        lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x) := by
      simpa [responseFramePlanarCoefficientField, blockCoeffField] using hmat
    have hl' : (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
        (hilbertBlockL2ToBlockL2 X x)).2 =
        (1 / 2 : ℝ) • (u.toH1.grad x-w.toH1.grad x) := by
      have ht := hl
      rw [← hpair] at ht
      exact ht
    calc
      lemmaVConjugateGradient ν σ (responseCoefficientExtension k x)
          (hilbertBlockL2ToBlockL2 X x) =
          (blockMatVecMul (blockCoeffField (responseFramePlanarCoefficientField ν σ k) x)
            (hilbertBlockL2ToBlockL2 X x)).2 := hmat'.symm
      _ = (1 / 2 : ℝ) • (u.toH1.grad x-w.toH1.grad x) := hl'
      _ = -g.grad x := by
        simp only [g, H1Function.smul_grad, H1Function.sub_grad]
        ext i
        change (1 / 2 : ℝ) * (u.toH1.grad x i-w.toH1.grad x i) =
          -((1 / 2 : ℝ) * (w.toH1.grad x i-u.toH1.grad x i))
        ring
  have hdensity : (fun x => responseFrameEnergyDensity ν σ
      (responseCoefficientExtension k x)
      (hilbertBlockL2ToBlockL2 X x)) =ᵐ[volumeMeasureOn U] fun x =>
        (ν / σ) * (vecNormSq (v.grad x) + vecNormSq (g.grad x)) := by
    filter_upwards [hfirst, hconj] with x hp hc
    rw [lemmaVFrameEnergy_split ν σ (responseCoefficientExtension k x)
      hν.ne' hσ.ne']
    rw [hp, hc]
    simp [vecNormSq, vecDot]
  have henergyDensity : D.energy X X = volumeAverage U (fun x =>
      responseFrameEnergyDensity ν σ (responseCoefficientExtension k x)
        (hilbertBlockL2ToBlockL2 X x)) := by
    rw [frameEnergy_eq_hilbert_integral (measurableSet_openCubeSet Q) hv
      ν σ hν hσ k X]
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2 X] with x hx
    rw [hx]
  have hnorm : D.energy X X = ‖S‖ ^ 2 := by
    change D.energy X X = ‖responseEnergyUp D X‖ ^ 2
    rw [energyCarrier_norm_sq, responseEnergyUp_down]
  have hAvgDensity : volumeAverage U (fun x => (ν / σ) *
      (vecNormSq (v.grad x) + vecNormSq (g.grad x))) =
      volumeAverage U (fun x => responseFrameEnergyDensity ν σ
        (responseCoefficientExtension k x) (hilbertBlockL2ToBlockL2 X x)) := by
    unfold volumeAverage
    congr 1
    exact integral_congr_ae hdensity.symm
  have hAvg : cubeAverage Q (fun x => (ν / σ) *
      (vecNormSq (v.grad x) + vecNormSq (g.grad x))) = ‖S‖ ^ 2 := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    change volumeAverage U (fun x => (ν / σ) *
      (vecNormSq (v.grad x) + vecNormSq (g.grad x))) = _
    rw [hAvgDensity, ← henergyDensity, hnorm]
  have hcoordV := main_coordinateEnergy_eq_cubeAverage_vecNormSq Q v.grad
    (fun i => v.grad_memL2_normalizedCubeMeasure i)
  have hcoordG := main_coordinateEnergy_eq_cubeAverage_vecNormSq Q g.grad
    (fun i => g.grad_memL2_normalizedCubeMeasure i)
  have hWeakV := main_tiledWeakHaarEnergy_le_coordinateEnergy Q m v.grad
    (fun i => v.grad_memL2_normalizedCubeMeasure i)
  have hWeakG := main_tiledWeakHaarEnergy_le_coordinateEnergy Q m g.grad
    (fun i => g.grad_memL2_normalizedCubeMeasure i)
  have hcoef : 0 ≤ ν / σ := div_nonneg hν.le hσ.le
  have hlin : (ν / σ) *
      ((∑ i : Fin 2, energy Q (fun x => v.grad x i)) +
       (∑ i : Fin 2, energy Q (fun x => g.grad x i))) =
      cubeAverage Q (fun x => (ν / σ) *
        (vecNormSq (v.grad x) + vecNormSq (g.grad x))) := by
    rw [hcoordV, hcoordG]
    have hIntV : Integrable (fun x => vecNormSq (v.grad x))
        (normalizedCubeMeasure Q) := by
      have hvec : (fun x => vecNormSq (v.grad x)) =
          fun x => ∑ i : Fin 2, (v.grad x i)^2 := by
        funext x
        simp [vecNormSq, vecDot, pow_two]
      rw [hvec]
      exact integrable_finsetSum _ fun i _ =>
        (v.grad_memL2_normalizedCubeMeasure i).integrable_sq
    have hIntG : Integrable (fun x => vecNormSq (g.grad x))
        (normalizedCubeMeasure Q) := by
      have hvec : (fun x => vecNormSq (g.grad x)) =
          fun x => ∑ i : Fin 2, (g.grad x i)^2 := by
        funext x
        simp [vecNormSq, vecDot, pow_two]
      rw [hvec]
      exact integrable_finsetSum _ fun i _ =>
        (g.grad_memL2_normalizedCubeMeasure i).integrable_sq
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [integral_const_mul, integral_add hIntV hIntG]
  have hsumWeak : lemmaVTiledWeakEnergy Q m v.grad +
      lemmaVTiledWeakEnergy Q m g.grad ≤
      (∑ i : Fin 2, energy Q (fun x => v.grad x i)) +
      (∑ i : Fin 2, energy Q (fun x => g.grad x i)) := add_le_add hWeakV hWeakG
  change (ν / σ) * (lemmaVTiledWeakEnergy Q m v.grad +
      lemmaVTiledWeakEnergy Q m g.grad) ≤ ‖S‖ ^ 2
  calc
    _ ≤ (ν / σ) * ((∑ i : Fin 2, energy Q (fun x => v.grad x i)) +
        (∑ i : Fin 2, energy Q (fun x => g.grad x i))) := mul_le_mul_of_nonneg_left hsumWeak hcoef
    _ = _ := hlin.trans hAvg

end ASDExplicitGamma.Main

end
