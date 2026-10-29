module

public import ASDExplicitGamma.Main.ObsLowerCoercivityVar
public import ASDExplicitGamma.Main.HotPatchSourceBound
public import ASDExplicitGamma.Main.HotPatchRow
public import ASDExplicitGamma.Native.OldSignedCanonicalResponseSpace
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledFeedback
public import ASDExplicitGamma.Variational.ForcedGradient

/-! Observer-level joint coercivity (source (1.2)) of the actual response pair, through the cell
history `B` and the forced joint bound with zero force; no ellipticity constant. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Native ASDExplicitGamma.Scalar

namespace ASDExplicitGamma.Main

/-- Weak Haar energy on a sub-cell only depends on the field almost everywhere on the parent
open cell. -/
theorem obs_weak_congr_ae (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure R))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure R))
    (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    vectorWeakHaarEnergy R F = vectorWeakHaarEnergy R G := by
  have hq : 1 < Real.sqrt 3 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
    simpa using h
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply lemmaV_dualEnergy_congr_ae R hq (hF i) (hG i)
  have h1 : ∀ᵐ x ∂(volume.restrict (openCubeSet R)), F x i = G x i :=
    ae_restrict_of_ae_restrict_of_subset hRQ (h.mono fun x hx => congrFun hx i)
  rw [Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet R)]
  exact h1

theorem obs_tiledWeak_congr_ae (Q : TriadicCube 2) (m : ℕ) {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    lemmaVTiledWeakEnergy Q m F = lemmaVTiledWeakEnergy Q m G := by
  unfold lemmaVTiledWeakEnergy descendantsAverage
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  exact obs_weak_congr_ae Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    (fun i => memLp_on_descendant_of_memLp hR (hF i))
    (fun i => memLp_on_descendant_of_memLp hR (hG i)) h

theorem obs_cubeIncrement_zero (R : TriadicCube 2) (j : ℕ) :
    cubeIncrement R j (fun _ : Vec 2 => (0 : ℝ)) = fun _ => 0 := by
  funext x
  by_cases hx : x ∈ cubeSet R
  · cases j with
    | zero => simp [cubeIncrement_zero, cubeProjection_const_of_mem_cubeSet R 0 0 hx]
    | succ j =>
      simp only [cubeIncrement_succ]
      rw [cubeProjection_const_of_mem_cubeSet R (j + 1) 0 hx,
        cubeProjection_const_of_mem_cubeSet R j 0 hx]
      simp
  · exact cubeIncrement_eq_zero_of_not_mem_cubeSet R j _ hx

theorem obs_energy_zero (R : TriadicCube 2) : energy R (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
  rw [energy_eq_integral_sq]
  simp

theorem obs_zero_series_term (R : TriadicCube 2) (i : Fin 2) (j : ℕ) :
    energy R (cubeIncrement R j (fun x => (fun _ : Vec 2 => (0 : Vec 2)) x i)) = 0 := by
  have h : (fun x : Vec 2 => (fun _ : Vec 2 => (0 : Vec 2)) x i) = fun _ => (0 : ℝ) := rfl
  rw [h, obs_cubeIncrement_zero]
  exact obs_energy_zero R

local instance obsPairFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The joint coercivity (1.2) of the actual response pair through the cell history `B`:
the tiled weak energies of the primal and reciprocal potentials together are at most `B`
times the minimizer energy. -/
theorem obs_response_pair_tiled_energy_le
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
          (responseFramePlanarCoefficientField ν σ k) u w).potential)
    (B : ℝ)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    let Q := originCube 2 n
    let U := openCubeSet Q
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r
    let g : H1Function U := (1 / 2 : ℝ) • (w.toH1 - u.toH1)
    let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    lemmaVTiledWeakEnergy Q m v.grad + lemmaVTiledWeakEnergy Q m g.grad ≤ B * ‖S‖ ^ 2 := by
  classical
  intro Q U v g S
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let a := responseFramePlanarCoefficientField ν σ k
  let M := responseFrameMuOperatorSystemData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let D := responseFrameEnergyData (measurableSet_openCubeSet Q) hv ν σ hν hσ k
  let X : HilbertBlockL2 U := M.toMuHilbertRealization.minimizerMap P
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ k
  let Wf : Vec 2 → BlockVec 2 :=
    (oldSignedFrameCanonicalField Q ν σ hν hσ k P : Vec 2 → BlockVec 2)
  let W : BlockState 2 := oldSignedCanonicalBlockState Q ν σ hν hσ k P
  have hcompat : ScalarCompatible U Wf := old_signed_canonical_compatible Q ν σ hν hσ k P
  have hresp := old_signed_canonical_response_space Q ν σ hν hσ k P
  have hWeval : W.eval = Wf := rfl
  have hWX : ∀ x, Wf x = hilbertBlockL2ToBlockL2 X x := fun x => rfl
  let uP : H1Function U := (1 / 2 : ℝ) • (u.toH1 - w.toH1)
  have hlower := blockResponse_lowerImage_pair_half_ae_eq_gradDiff_of_isEllipticFieldOn
    a hEll u w
  have hlowerAE : (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) =ᵐ[
      volumeMeasureOn U] uP.grad := by
    filter_upwards [hrep, hlower] with x hx hl
    have hpair : W.eval x = (blockResponsePairHalfState a u w).eval x := by
      rw [hWeval, hWX]; exact hx
    rw [hpair]
    have ht := hl
    simpa [uP, H1Function.smul_grad, H1Function.sub_grad] using ht
  have hforcedRoot : ∀ T : BlockState 2, ScalarVariation U T.eval →
      volumeAverage U (blockPairingIntegrand a T W) =
        volumeAverage U (fun x => vecDot (T.potential x) ((fun _ => (0 : Vec 2)) x)) := by
    intro T hT
    have htest : IsBlockTestOn U T := ⟨hT.2.1, hT.2.2⟩
    have h0 := hresp.2.2 T htest
    unfold volumeAverage
    have : ∫ x in U, blockPairingIntegrand a T W x ∂volume = 0 := h0
    rw [this]
    simp [vecDot]
  have hint : IntegrableOn (blockPairingIntegrand a W W) (cubeSet Q) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
      (blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (hWeval ▸ hcompat.1) (hWeval ▸ hcompat.1) hEll)
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q m) :
      vectorWeakHaarEnergy R W.potential + vectorWeakHaarEnergy R uP.grad ≤
        B * cubeAverage R (blockPairingIntegrand a W W) := by
    let Vset := openCubeSet R
    letI : IsFiniteMeasure (volumeMeasureOn Vset) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    have hRQ : Vset ⊆ U := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
    have hcR : ScalarCompatible Vset Wf := old_signed_compatible_restrict Q R hRQ hcompat
    have hWmemR : MemBlockL2 Vset W.eval := hWeval ▸ hcR.1
    have hWpotR : IsBlockPotentialOn Vset W := hcR.2.1
    have hWsolR : IsBlockSolenoidalOn Vset W := hcR.2.2
    have hWlowerR : MemVectorL2 Vset
        (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) := by
      have hm : MemVectorL2 Vset uP.grad :=
        uP.grad_memVectorL2.mono_measure (Measure.restrict_mono_set volume hRQ)
      exact hm.ae_eq (ae_restrict_of_ae_restrict_of_subset hRQ hlowerAE.symm)
    have hG : MemLp (fun _ : Vec 2 => (0 : Vec 2)) 2 (normalizedCubeMeasure R) :=
      memLp_const _
    have hGpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy R (cubeIncrement R (j + 1) (fun x => (fun _ : Vec 2 => (0 : Vec 2)) x i))) := by
      intro i
      simp only [obs_zero_series_term, mul_zero]
      exact summable_zero
    have hforcedR := forcedSource_weakEquation_onDescendant Q m R hR W
      (fun _ => (0 : Vec 2)) hforcedRoot
    let uR := uP.restrictToOpenSubcube hR
    have huR : (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) =ᵐ[
        volumeMeasureOn Vset] uR.grad :=
      ae_restrict_of_ae_restrict_of_subset hRQ hlowerAE
    obtain ⟨X0, hX0, hj, hg⟩ := pureFlux_forced_pair_joint_bound R hEllR W hWpotR hWsolR
      hWmemR hWlowerR hG hGpos hforcedR uR huR
    have hcirc : forcedSourceCircleEnergy R (fun _ => (0 : Vec 2)) = 0 := by
      apply le_antisymm _ (forcedSourceCircleEnergy_nonneg R _)
      refine (pureFlux_forcedSourceCircleEnergy_le R _).trans (le_of_eq ?_)
      unfold vectorPositiveHaarEnergy primalEnergy
      simp only [obs_zero_series_term, mul_zero, tsum_zero]
      simp
    have hweak : vectorWeakHaarEnergy R uP.grad ≤ X0 := by
      have h1 := hg
      rw [hcirc, Real.sqrt_zero, mul_zero, add_zero] at h1
      have h2 : vectorWeakHaarEnergy R uR.grad ≤ X0 :=
        (Real.sqrt_le_sqrt_iff hX0).1 h1
      exact h2
    have heq : blockPairingAverage Vset a W W = cubeAverage R (blockPairingIntegrand a W W) := by
      rw [blockPairingAverage, cubeAverage_eq_integralAverage_openCubeSet]
      rfl
    have hE0 : 0 ≤ blockPairingAverage Vset a W W :=
      compatible_blockPairingAverage_nonneg hEllR W
    calc vectorWeakHaarEnergy R W.potential + vectorWeakHaarEnergy R uP.grad
        ≤ vectorWeakHaarEnergy R W.potential + X0 := add_le_add le_rfl hweak
      _ = X0 + vectorWeakHaarEnergy R W.potential := add_comm _ _
      _ ≤ _ := hj.trans (mul_le_mul_of_nonneg_right (hhist R hR) hE0)
      _ = _ := by rw [heq]
  have hnorm : D.energy X X = ‖S‖ ^ 2 := by
    change D.energy X X = ‖responseEnergyUp D X‖ ^ 2
    rw [energyCarrier_norm_sq, responseEnergyUp_down]
  have hSE : ‖S‖ ^ 2 = cubeAverage Q (blockPairingIntegrand a W W) := by
    rw [← hnorm]
    change M.toMuHilbertRealization.energyBilin X X = _
    rw [lemmaV_muSystem_bilinear_eq_volumeAverage, cubeAverage_eq_integralAverage_openCubeSet Q]
    rfl
  have hpotMem (i : Fin 2) : MemLp (fun x => W.potential x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2 (show MemBlockL2 U W.eval from hcompat.1)) i)
  have hpotAE : W.potential =ᵐ[volumeMeasureOn U] v.grad := by
    filter_upwards [hrep, hgrad] with x hx hg
    have h1 : W.potential x = (blockResponsePairHalfState a u w).potential x := by
      have := congrArg Prod.fst (show Wf x = (blockResponsePairHalfState a u w).eval x by
        rw [hWX]; exact hx)
      exact this
    rw [h1, ← hg]
  have hgneg : g.grad = fun x i => -(uP.grad x i) := by
    funext x i
    simp only [g, uP, H1Function.smul_grad, H1Function.sub_grad]
    change (1 / 2 : ℝ) * (w.toH1.grad x i - u.toH1.grad x i) =
      -((1 / 2 : ℝ) * (u.toH1.grad x i - w.toH1.grad x i))
    ring
  have hWv : lemmaVTiledWeakEnergy Q m v.grad = lemmaVTiledWeakEnergy Q m W.potential :=
    (obs_tiledWeak_congr_ae Q m hpotMem
      (fun i => v.grad_memL2_normalizedCubeMeasure i) hpotAE).symm
  have hWg : lemmaVTiledWeakEnergy Q m g.grad = lemmaVTiledWeakEnergy Q m uP.grad := by
    rw [hgneg]
    unfold lemmaVTiledWeakEnergy descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro R _
    exact vectorWeakHaarEnergy_neg_hot R uP.grad
  have hEavg : descendantsAverage Q m (fun R => cubeAverage R (blockPairingIntegrand a W W)) =
      cubeAverage Q (blockPairingIntegrand a W W) :=
    (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q m _ hint).symm
  have hsumAvg : lemmaVTiledWeakEnergy Q m W.potential + lemmaVTiledWeakEnergy Q m uP.grad =
      descendantsAverage Q m (fun R => vectorWeakHaarEnergy R W.potential +
        vectorWeakHaarEnergy R uP.grad) := by
    unfold lemmaVTiledWeakEnergy
    rw [descendantsAverage_add]
  rw [hWv, hWg, hsumAvg, hSE, ← hEavg, ← descendantsAverage_mul_left]
  exact descendantsAverage_le fun R hR => hcell R hR

end ASDExplicitGamma.Main
