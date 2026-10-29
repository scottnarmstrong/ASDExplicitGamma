module

public import ASDExplicitGamma.Inverse.HybridGradientConstants
public import ASDExplicitGamma.Inverse.CountableResponseAE
public import ASDExplicitGamma.Inverse.RestrictedResponseCoefficients
public import ASDExplicitGamma.Inverse.StoppedKuhnFlux

/-! The actual countable hybrid variational comparison. All loadings use
one common midpoint map and one common physical hybrid dissection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- Countable hybrid subadditivity for the actual full-UV target and the
actual common loading map. Domain geometry, local coefficient identities,
and global flux admissibility are all discharged internally. -/
theorem actual_hybrid_variational_comparison (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (m J : ℤ) (hm : m ≤ J) (weights : ℤ → ℝ) :
    ∃ C : HybridCell Q H S → Mat 2,
      (∀ i : HybridIdentityCell Q H S, C (.inl i)=1) ∧
      (∀ i, (hybridParent i).2.val ∈ S → C i=0) ∧
      (∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=C i) ∧
      (∀ q : Vec 2,
        ENNReal.ofReal (dotProduct q ((coarseBlockMatrix (cubeSet Q)
          (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤
        ∑' i : HybridCell Q H S, ENNReal.ofReal
          (((volume (hybridDomain i:Set (Vec 2))).toReal/(volume (openCubeSet Q)).toReal)*
            dotProduct (matVecMul (planarFluxMatrix (C i)) q)
              ((coarseBlockMatrix (hybridDomain i:Set (Vec 2))
                (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec
                  (matVecMul (planarFluxMatrix (C i)) q)))) := by
  obtain ⟨C,hCi,hCb,hCa⟩ := hybrid_common_gradient_constants M Q H hH τ η ω hgood S hS hbad
  refine ⟨C,hCi,hCb,hCa,?_⟩
  intro q
  let k := oldResponseCoefficient Q m ω+
    laterResponseCoefficient Q m J (sourceBandWeights m weights) ω
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos k
  let aS := fun i : HybridCell Q H S => restrictCoeffOn aQ (hybrid_domain_subset_root i)
  have hF : Book.Ch01.PotentialZeroTraceFieldOn (openCubeSet Q) (fun _ : Vec 2 => (0:Vec 2)-0) := by
    simpa using (Whitney.potentialZeroTraceFieldOn_zero (U := openCubeSet Q))
  have hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet Q)
      (fun x => matVecMul (planarFluxMatrix
        (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q-q) :=
    stopped_kuhn_flux_admissible M Q H hH τ η ω hgood S hS hbad q
  have hcmp := countable_response_le_of_ae_constant aQ aS (fun _ => rfl)
    hybrid_domain_subset_root (hybrid_domains_disjoint Q H S) (hybrid_domains_cover Q H S)
    0 q (fun _ => 0)
    (fun x => matVecMul (planarFluxMatrix (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q)
    (fun _ => 0) (fun i => matVecMul (planarFluxMatrix (C i)) q) hF hG
    (fun _ => Filter.Eventually.of_forall (fun _ _ => rfl)) (by
      intro i
      filter_upwards [hCa i] with x hx
      intro hxcell
      rw [hx hxcell])
  have hroot : Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ=
      coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω) :=
    attenuated_sensitivity_matrix_eq M Q m m J le_rfl hm weights ω
  have hcell (i : HybridCell Q H S) : Book.Ch02.coarseBlockMatrix (hybridDomain i) (aS i)=
      coarseBlockMatrix (hybridDomain i:Set (Vec 2)) (attenuatedCoefficient M m J weights ω) :=
    attenuated_domain_matrix_eq M Q m m J le_rfl hm weights ω (hybridDomain i)
      (hybrid_domain_subset_root i)
  rw [hroot] at hcmp
  simpa only [hcell,← lower_right_quadratic,Book.Ch02.cubeDomain_coe] using hcmp

end
end ASDExplicitGamma.Inverse
