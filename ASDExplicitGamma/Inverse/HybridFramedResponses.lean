module

public import ASDExplicitGamma.Inverse.HybridFrameComparison
public import ASDExplicitGamma.Inverse.ClippedMatrixPositiveSums

/-! Both actual hybrid energies in the single true root frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- Whole identity-cell energy with its exact source frame clock and
physical normalized volume. -/
theorem hybrid_identity_framed_response (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (i : HybridIdentityCell Q H (rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω)) (q : Vec 2) :
    let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
    let w := (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (i.val.1-1):ℝ))
    (Annealed.sigmaBar M m:ℝ)*(volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*
      dotProduct q ((coarseBlockMatrix (hybridDomain (.inl i):Set (Vec 2))
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q) ≤
      G*rootEdelta r*(w*(volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal*
        fullMatrixQuadratic (toFullBlockVec (0,q))
          (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val (rootTau r) ω)) := by
  have h333 : 333 ≤ H := (show 333 ≤ rootH0 r by cases r <;> norm_num [rootH0]).trans hH
  have hlocal := hybrid_identity_response_bound M Q H h333 r ω m J hQ hm weights hw i q
  have hr := hybrid_parent_true_frame_ratio M Q H r hH _ m hQ (.inl i)
  have hB : 0 ≤ rootEdelta r*fullMatrixQuadratic (toFullBlockVec (0,q))
      (clippedCellMatrix M (i.val.2.val.scale+40) i.val.2.val (rootTau r) ω) :=
    mul_nonneg (Real.exp_pos _).le (clipped_cell_matrix_quadratic_nonneg M _ _ _ ω _)
  have hh := convert_local_frame_energy (Annealed.sigmaBar_characterization M m).1.le
    (Annealed.sigmaBar_characterization M (i.val.2.val.scale+40)).1 hlocal hB hr
  have hf := mul_le_mul_of_nonneg_left hh (div_nonneg
    (ENNReal.toReal_nonneg (a := volume (cubeSet i.val.2.val))) (ENNReal.toReal_nonneg (a := volume (cubeSet Q))))
  dsimp only [hybridParent] at hf
  dsimp only
  convert hf using 1 <;> ring

/-- Active-simplex energy in the same true root frame, with the source
g(6 tau) and exact layer clock. Bad-parent energies are already zero. -/
theorem hybrid_active_framed_response (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω) → Mat 2)
    (hCb : ∀ i, (hybridParent i).2.val ∈ rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω → C i=0)
    (i : HybridActiveCell Q H (rootBadWhitneyCells M Q H (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) ω)) (q : Vec 2) :
    let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
    let w := (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (i.1.val.1-1):ℝ))
    let v := matVecMul (planarFluxMatrix (C (.inr i))) q
    (Annealed.sigmaBar M m:ℝ)*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*
      dotProduct v ((coarseBlockMatrix (hybridDomain (.inr i):Set (Vec 2))
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
      G*rootEdelta r*rootResponseEnvelope (6*rootTau r)*
        (w*(volume (hybridDomain (.inr i):Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal*dotProduct v v) := by
  have h333 : 333 ≤ H := (show 333 ≤ rootH0 r by cases r <;> norm_num [rootH0]).trans hH
  have hlocal := hybrid_active_response_bound M Q H h333 r ω m J hQ hm weights hw C hCb i q
  have hr := hybrid_parent_true_frame_ratio M Q H r hH _ m hQ (.inr i)
  have hτ : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hB : 0 ≤ rootEdelta r*rootResponseEnvelope (6*rootTau r)*
      dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q) (matVecMul (planarFluxMatrix (C (.inr i))) q) := by
    have hv : 0 ≤ dotProduct (matVecMul (planarFluxMatrix (C (.inr i))) q)
        (matVecMul (planarFluxMatrix (C (.inr i))) q) := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    unfold rootEdelta rootResponseEnvelope
    positivity
  have hh := convert_local_frame_energy (Annealed.sigmaBar_characterization M m).1.le
    (Annealed.sigmaBar_characterization M (i.1.val.2.val.scale+40)).1 hlocal hB hr
  have hf := mul_le_mul_of_nonneg_left hh (div_nonneg
    (ENNReal.toReal_nonneg (a := volume (hybridDomain (.inr i):Set (Vec 2))))
      (ENNReal.toReal_nonneg (a := volume (cubeSet Q))))
  dsimp only [hybridParent] at hf
  dsimp only
  convert hf using 1 <;> ring

end
end ASDExplicitGamma.Inverse
