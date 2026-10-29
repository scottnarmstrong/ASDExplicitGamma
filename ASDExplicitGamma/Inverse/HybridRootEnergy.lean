module

public import ASDExplicitGamma.Inverse.HybridVariationalComparison
public import ASDExplicitGamma.Inverse.HybridFramedResponses

/-! The complete actual hybrid energy in the one true root frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual root energy is bounded by the complete positive identity and
active sums with the exact true-frame clocks. One slope family serves every
flux loading, and all local response and frame-ratio inputs are discharged. -/
theorem actual_hybrid_root_energy_split (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau r)
        (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) k (rootBlockStart Q k))
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) :
    let S := rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω
    let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
    let w := fun n => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (n-1):ℝ))
    ∃ C : HybridCell Q H S → Mat 2,
      (∀ i : HybridIdentityCell Q H S, C (.inl i)=1) ∧
      (∀ i, (hybridParent i).2.val ∈ S → C i=0) ∧
      (∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ (hybridDomain i:Set (Vec 2)) →
        stoppedKuhnGradient M Q H (show 333 ≤ H from
          (show 333 ≤ rootH0 r by cases r <;> norm_num [rootH0]).trans hH)
          (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω hgood S
          (fun _ h => h.1) (fun _ h => h.2) x=C i) ∧
      (∀ q : Vec 2,
        ENNReal.ofReal ((Annealed.sigmaBar M m:ℝ)*dotProduct q ((coarseBlockMatrix (cubeSet Q)
          (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤
        ENNReal.ofReal (G*rootEdelta r)*
          ((∑' i : HybridIdentityCell Q H S, ENNReal.ofReal
            (w i.val.1*(volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*
              fullMatrixQuadratic (toFullBlockVec (0,q))
                (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val (rootTau r) ω)))+
          ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*
            ∑' i : HybridActiveCell Q H S, ENNReal.ofReal
              (w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*
                dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q)
                  (matVecMul (planarFluxMatrix (C (.inr i))) q)))) := by
  classical
  dsimp only
  let τ := rootTau r
  let η := ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)
  let S := rootBadWhitneyCells M Q H τ η ω
  let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
  let w := fun n : ℕ => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (n-1):ℝ))
  have h333 : 333 ≤ H := (show 333 ≤ rootH0 r by cases r <;> norm_num [rootH0]).trans hH
  have hS : S ⊆ whitneyRootPartition Q H := fun _ h => h.1
  have hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V := fun _ h => h.2
  obtain ⟨C,hCi,hCb,hCa,hvar⟩ := actual_hybrid_variational_comparison M Q H h333 τ η ω hgood S hS hbad m J hm weights
  refine ⟨C,hCi,hCb,hCa,?_⟩
  intro q
  let σ := (Annealed.sigmaBar M m:ℝ)
  let b := fun i : HybridCell Q H S => matVecMul (planarFluxMatrix (C i)) q
  let F := fun i : HybridCell Q H S => σ*(volume (hybridDomain i:Set (Vec 2))).toReal/
    (volume (cubeSet Q)).toReal*dotProduct (b i)
      ((coarseBlockMatrix (hybridDomain i:Set (Vec 2)) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec (b i))
  let fi := fun i : HybridIdentityCell Q H S => w i.val.1*(volume (cubeSet i.val.2.val)).toReal/
    (volume (cubeSet Q)).toReal*fullMatrixQuadratic (toFullBlockVec (0,q))
      (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val τ ω)
  let fa := fun i : HybridActiveCell Q H S => w i.1.val.1*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/
    (volume (cubeSet Q)).toReal*dotProduct (b (.inr i)) (b (.inr i))
  have hσ : 0 ≤ σ := (Annealed.sigmaBar_characterization M m).1.le
  have hGE : 0 ≤ G*rootEdelta r := mul_nonneg (by dsimp only [G]; positivity) (Real.exp_pos _).le
  have hτ : 0 ≤ τ := by cases r <;> norm_num [τ,rootTau]
  have hg : 0 ≤ rootResponseEnvelope (6*τ) := by unfold rootResponseEnvelope; positivity
  have hroot : ENNReal.ofReal (σ*dotProduct q ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤ ∑' i, ENNReal.ofReal (F i) := by
    have hh := mul_le_mul_right (hvar q) (ENNReal.ofReal σ)
    rw [← ENNReal.ofReal_mul hσ,← ENNReal.tsum_mul_left] at hh
    apply hh.trans_eq
    apply tsum_congr
    intro i
    rw [← ENNReal.ofReal_mul hσ]
    have he : volume (openCubeSet Q)=volume (cubeSet Q) := (measure_congr (cubeSet_ae_eq_openCubeSet Q)).symm
    rw [he]
    congr 1
    dsimp only [F,b]
    ring
  let R : HybridCell Q H S → ℝ≥0∞ := Sum.elim
    (fun i => ENNReal.ofReal (G*rootEdelta r)*ENNReal.ofReal (fi i))
    (fun i => ENNReal.ofReal (G*rootEdelta r*rootResponseEnvelope (6*τ))*ENNReal.ofReal (fa i))
  have hterm (i : HybridCell Q H S) : ENNReal.ofReal (F i) ≤ R i := by
    cases i with
    | inl i =>
      change ENNReal.ofReal (F (.inl i)) ≤ ENNReal.ofReal (G*rootEdelta r)*ENNReal.ofReal (fi i)
      rw [← ENNReal.ofReal_mul hGE]
      apply ENNReal.ofReal_le_ofReal
      have hh := hybrid_identity_framed_response M Q H r hH ω m J hQ hm weights hw i q
      have hOne : matVecMul (1:Mat 2) q=q := by ext k; simp [matVecMul,Matrix.one_apply]
      have he : volume (hybridDomain (.inl i):Set (Vec 2))=volume (cubeSet i.val.2.val) :=
        (measure_congr (cubeSet_ae_eq_openCubeSet i.val.2.val)).symm
      simpa only [F,b,hCi i,planar_flux_matrix_one,hOne,he,G,w,fi,σ,τ] using hh
    | inr i =>
      change ENNReal.ofReal (F (.inr i)) ≤ ENNReal.ofReal (G*rootEdelta r*rootResponseEnvelope (6*τ))*ENNReal.ofReal (fa i)
      rw [← ENNReal.ofReal_mul (mul_nonneg hGE hg)]
      exact ENNReal.ofReal_le_ofReal (hybrid_active_framed_response M Q H r hH ω m J hQ hm weights hw C hCb i q)
  have hsum := hroot.trans (ENNReal.tsum_le_tsum hterm)
  apply hsum.trans_eq
  change (∑' i : HybridIdentityCell Q H S ⊕ HybridActiveCell Q H S, R i)=_
  rw [ENNReal.summable.tsum_sum ENNReal.summable]
  change (∑' i : HybridIdentityCell Q H S, ENNReal.ofReal (G*rootEdelta r)*ENNReal.ofReal (fi i))+
    (∑' i : HybridActiveCell Q H S, ENNReal.ofReal (G*rootEdelta r*rootResponseEnvelope (6*τ))*ENNReal.ofReal (fa i))=_
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left,ENNReal.ofReal_mul hGE,mul_add,mul_assoc]

end
end ASDExplicitGamma.Inverse
