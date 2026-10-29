module

public import ASDExplicitGamma.Inverse.HybridVariationalComparison
public import ASDExplicitGamma.Inverse.StoppedKuhnLoadCoordinates
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Variational.LemmaVSobolev

/-! The actual common Kuhn map admits both the potential and flux parts of
the full block variational comparison, for every paired loading. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney Algsuperdiff.Section3.Provider.Multiscale
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

local instance stoppedKuhnFullComparisonFiniteVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Full block comparison for the actual stopped planar map. The potential
loading is its weak gradient and the flux loading is the source planar
antisymmetric companion, both built from the same midpoint interpolant. -/
theorem actual_hybrid_full_variational_comparison
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
    (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (m J : ℤ) (hm : m ≤ J) (weights : ℤ → ℝ)
    (C : HybridCell Q H S → Mat 2)
    (hCa : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ (hybridDomain i : Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x = C i)
    (p q : Vec 2) :
    ENNReal.ofReal (blockVecDot (p,q) (blockMatVecMul
      (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M m J weights ω)) (p,q))) ≤
      ∑' i : HybridCell Q H S, ENNReal.ofReal
        (((volume (hybridDomain i : Set (Vec 2))).toReal /
            (volume (openCubeSet Q)).toReal) *
          blockVecDot (matVecMul (C i) p,
              matVecMul (planarFluxMatrix (C i)) q)
            (blockMatVecMul
              (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
                (attenuatedCoefficient M m J weights ω))
              (matVecMul (C i) p, matVecMul (planarFluxMatrix (C i)) q))) := by
  let F := fun x : Vec 2 => matVecMul
    (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x) p
  let G := fun x : Vec 2 => matVecMul
    (planarFluxMatrix (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q
  let aQ := sensitivityBookCoeffOn Q M.nu M.nu_pos
    (oldResponseCoefficient Q m ω +
      laterResponseCoefficient Q m J (sourceBandWeights m weights) ω)
  let aS := fun i : HybridCell Q H S => restrictCoeffOn aQ
    (hybrid_domain_subset_root i)
  have hF : Book.Ch01.PotentialZeroTraceFieldOn (openCubeSet Q)
      (fun x => F x - p) := by
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let affine := ASDExplicitGamma.Variational.lemmaVAffinePotential hU p
      (0 : H10Function (openCubeSet Q))
    let interp := stoppedKuhnMidpointLinearInterpolant M Q H hH τ η ω hgood S hS hbad
    let residual := affine - interp affine
    have hmem : MemH10 (openCubeSet Q) residual.toFun :=
      stopped_kuhn_midpoint_interpolant_residual_memH10
        M Q H hH τ η ω hgood S hS hbad p 0
    obtain ⟨r, hr⟩ := hmem
    have hgrad : r.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
        residual.grad :=
      ASDExplicitGamma.Variational.lemmaV_H1_grad_eq_ae
        (isOpen_openCubeSet Q) hr
    have hload (x : Vec 2) : (interp affine).grad x = F x := by
      rw [stopped_kuhn_interpolant_affine_coordinates
        M Q H hH τ η ω hgood S hS hbad p 0]
      ext k
      simp [F, stoppedKuhnGradient, matVecMul, Fin.sum_univ_two,
        H1Function.smul_grad]
      ring
    have hfield : (fun x => F x - p) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => (-r).toH1Function.grad x := by
      filter_upwards [hgrad] with x hx
      ext k
      have hzgrad : (0 : H10Function (openCubeSet Q)).toH1Function.grad x k = 0 := rfl
      have hax : affine.grad x k = p k := by
        simp [affine, ASDExplicitGamma.Variational.lemmaVAffinePotential,
          H1Function.add_grad,
          H1Function.affineOnIsSobolevRegularDomain_grad]
        rw [hzgrad]
      have hxk : r.toH1Function.grad x k = residual.grad x k :=
        congrArg (fun v : Vec 2 => v k) hx
      have hxk' : r.toH1Function.grad x k =
          affine.grad x k - (interp affine).grad x k := by
        simpa only [residual, H1Function.sub_grad, Pi.sub_apply] using hxk
      rw [hload x, hax] at hxk'
      have hrx : r.toH1Function.grad x k = p k - F x k := by
        exact hxk'
      have hneg : (-r).toH1Function.grad x k = -r.toH1Function.grad x k := by
        change ((-1 : ℝ) • r.toH1Function).grad x k = _
        simp
      change F x k - p k = (-r).toH1Function.grad x k
      rw [hneg, hrx]
      ring
    have hz := Book.Ch01.potentialZeroTraceFieldOn_of_h10 (-r)
    exact ⟨hz.1.ae_eq hfield.symm, -r, hfield.trans Filter.EventuallyEq.rfl⟩
  have hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (openCubeSet Q)
      (fun x => matVecMul (planarFluxMatrix
        (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q-q) :=
    stopped_kuhn_flux_admissible M Q H hH τ η ω hgood S hS hbad q
  have hFc (i : HybridCell Q H S) :
      ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        x ∈ (hybridDomain i : Set (Vec 2)) → F x = matVecMul (C i) p := by
    filter_upwards [hCa i] with x hx
    intro hxcell
    change matVecMul (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x) p = _
    rw [hx hxcell]
  have hGc (i : HybridCell Q H S) :
      ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        x ∈ (hybridDomain i : Set (Vec 2)) →
          G x = matVecMul (planarFluxMatrix (C i)) q := by
    filter_upwards [hCa i] with x hx
    intro hxcell
    change matVecMul (planarFluxMatrix
      (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q = _
    rw [hx hxcell]
  have hcmp := countable_response_le_of_ae_constant aQ aS (fun _ => rfl)
    hybrid_domain_subset_root (hybrid_domains_disjoint Q H S)
    (hybrid_domains_cover Q H S) p q F G
    (fun i => matVecMul (C i) p)
    (fun i => matVecMul (planarFluxMatrix (C i)) q) hF hG hFc hGc
  have hroot : Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) aQ =
      coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω) :=
    attenuated_sensitivity_matrix_eq M Q m m J le_rfl hm weights ω
  have hcell (i : HybridCell Q H S) :
      Book.Ch02.coarseBlockMatrix (hybridDomain i) (aS i) =
        coarseBlockMatrix (hybridDomain i : Set (Vec 2))
          (attenuatedCoefficient M m J weights ω) :=
    attenuated_domain_matrix_eq M Q m m J le_rfl hm weights ω
      (hybridDomain i) (hybrid_domain_subset_root i)
  rw [hroot] at hcmp
  simpa only [hcell, Book.Ch02.cubeDomain_coe] using hcmp

/-- Summing the full-pair variational comparison over the four normalized
frame loads gives the complete framed-trace comparison, before applying the
identity-cell shear and active-cell amplitude caps. -/
theorem actual_hybrid_full_four_load_comparison
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
    (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (m J : ℤ) (hm : m ≤ J) (weights : ℤ → ℝ)
    (C : HybridCell Q H S → Mat 2)
    (hCa : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ (hybridDomain i : Set (Vec 2)) →
        stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x = C i)
    (σ : ℝ) (hσ : 0 < σ) :
    (∑ j : Fin 2 × Bool, ENNReal.ofReal (by
      let P := fullResponseTraceLoad j
      let Pσ := ((Real.sqrt σ)⁻¹ • P.1, Real.sqrt σ • P.2)
      exact blockVecDot Pσ (blockMatVecMul
        (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)) Pσ))) ≤
    ∑ j : Fin 2 × Bool, ∑' i : HybridCell Q H S, ENNReal.ofReal (by
      let P := fullResponseTraceLoad j
      let Pσ := ((Real.sqrt σ)⁻¹ • P.1, Real.sqrt σ • P.2)
      exact ((volume (hybridDomain i : Set (Vec 2))).toReal /
          (volume (openCubeSet Q)).toReal) *
        blockVecDot (matVecMul (C i) Pσ.1,
          matVecMul (planarFluxMatrix (C i)) Pσ.2)
          (blockMatVecMul
            (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
              (attenuatedCoefficient M m J weights ω))
            (matVecMul (C i) Pσ.1,
              matVecMul (planarFluxMatrix (C i)) Pσ.2))) := by
  classical
  apply Finset.sum_le_sum
  intro j hj
  let P := fullResponseTraceLoad j
  let Pσ := ((Real.sqrt σ)⁻¹ • P.1, Real.sqrt σ • P.2)
  simpa only [P, Pσ] using
    (actual_hybrid_full_variational_comparison M Q H hH τ η ω hgood S hS hbad
      m J hm weights C hCa Pσ.1 Pσ.2)

end
end ASDExplicitGamma.Inverse
