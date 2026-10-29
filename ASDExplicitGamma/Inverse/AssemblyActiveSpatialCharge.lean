module

public import ASDExplicitGamma.Inverse.AssemblyWeightedActiveCharge
public import ASDExplicitGamma.Inverse.AssemblyActiveMean
public import ASDExplicitGamma.Inverse.AssemblyReferenceEnergy

/-! The actual parent wave means are charged against the actual geometric density. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Conversion from the normalized physical square to its restricted volume. -/
theorem assembly_ae_cube_of_ae_normalized (Q : TriadicCube 2) (P : Vec 2 → Prop)
    (hP : ∀ᵐ x ∂normalizedCubeMeasure Q, P x) :
    ∀ᵐ x ∂volumeMeasureOn (cubeSet Q), P x := by
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  change ∀ᵐ x ∂ENNReal.ofReal ((cubeVolume Q)⁻¹) • volume.restrict (cubeSet Q), P x at hP
  exact (Measure.ae_ennreal_smul_measure_iff hc).mp hP

/-- The common spatial payment on a deterministic layer uses its exact old
label and the actual attenuated band, with no selected random mask. -/
def assemblyActiveSpatialPayment (M : ABKModel 2) (Q : TriadicCube 2)
    (k H n : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) : ℝ :=
  1+32*(10*waveGateEta .allOrder)^2+
    2*(laterScalarBand (layerOldCutoff Q.scale H n) N
      (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω x/
        Annealed.sigmaBar M (layerOldCutoff Q.scale H n))^2

/-- The scalar mean payment assigned to each active cell, prior to multiplication
by the common slope's squared operator norm. -/
def assemblyActiveParentMeanPayment (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (S : Set (TriadicCube 2)) (N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (i : HybridActiveCell Q H S) : ℝ :=
  let P := i.1.val.2.val
  let n := P.scale+40
  1+(|cubeAverage P (laterBandW2 P n N
    (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω).value.toFun/
      Annealed.sigmaBar M n|+2*(10*waveGateEta .allOrder))^2

/-- Actual parent means and actual common slopes are paid by spatial wave
weights times the same three geometric resolution squares. All regularity
and local mean premises are supplied internally. -/
theorem assembly_active_parent_mean_charge (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (hH : heightEntrance k ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) resetAllOrderTau (waveGateEta .allOrder)) j (rootBlockStart Q j))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)) ω z ≠ ∞)
    (N : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N, 0 ≤ weights n ∧ weights n ≤ 1)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω) → Mat 2)
    (hCb : ∀ i, (hybridParent i).2.val ∈
      rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω → C i=0)
    (hCa : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
      stoppedKuhnGradient M Q H (show 333 ≤ H by unfold heightEntrance at hH; omega)
        resetAllOrderTau (waveGateEta .allOrder) ω hgood
        (rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω)
        (fun _ h => h.1) (fun _ h => h.2) x=C i)
    (w : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ w n) :
    let S := rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω
    (∑' i : HybridActiveCell Q H S, ENNReal.ofReal
      (w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*
        (‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2*
          assemblyActiveParentMeanPayment M Q k H S N weights ω i))) ≤
      ∑' n : ℕ, ENNReal.ofReal (w n*(planarGradientCharge 40+1)/(volume (cubeSet Q)).toReal*
        ∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
          (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder) n e ω x)^2*
            assemblyActiveSpatialPayment M Q k H n N weights ω x) := by
  let S := rootBadWhitneyCells M Q H resetAllOrderTau (waveGateEta .allOrder) ω
  have h333 : 333 ≤ H := by unfold heightEntrance at hH; omega
  apply assembly_weighted_active_charge M Q H h333 resetAllOrderTau (waveGateEta .allOrder)
    ω hgood S (fun _ h => h.1) (fun _ h => h.2) hfinite C hCa
    (assemblyActiveSpatialPayment M Q k H · N weights ω) (fun n x => by
      unfold assemblyActiveSpatialPayment
      positivity)
    (fun n e => assembly_density_square_mul_continuous_integrable M Q H h333 _ _ n e ω _ (by
      unfold assemblyActiveSpatialPayment
      exact continuous_const.add (continuous_const.mul
        (((later_scalar_band_contDiff _ N _ ω).continuous.div_const _).pow 2))))
    (fun i => ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2*
      assemblyActiveParentMeanPayment M Q k H S N weights ω i) ?_ w hw0
  intro i
  by_cases hb : (hybridParent (.inr i)).2.val ∈ S
  · have hz := hCb (.inr i) hb
    simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul,le_refl,Filter.eventually_true]
  · let P := i.1.val.2.val
    let n := i.1.val.1
    have hlabel := root_whitney_old_cutoff_eq Q H n i.1.val.2.property
    have hparent := hybrid_parent_good_of_not_bad M Q H resetAllOrderTau (waveGateEta .allOrder) ω (.inr i) hb
    have hh := assembly_good_parent_pointwise_mean_payment M P (protectedOldLabel Q.scale k)
      N weights hw ω hparent
    have hh' := assembly_ae_cube_of_ae_normalized P _ hh
    have hsub : (hybridDomain (.inr i):Set (Vec 2)) ⊆ cubeSet P :=
      (hybrid_domain_subset_parent (.inr i)).trans (openCubeSet_subset_cubeSet P)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hh'] with x hx
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    dsimp only [assemblyActiveParentMeanPayment,assemblyActiveSpatialPayment]
    rw [hlabel]
    exact hx

end
end ASDExplicitGamma.Inverse
