module

public import ASDExplicitGamma.Inverse.HybridRootEnergy
public import ASDExplicitGamma.Inverse.HybridActiveSum
public import ASDExplicitGamma.Inverse.HybridIdentitySum

/-! Actual root energy paid by full deterministic layer means and densities. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The root response is bounded by complete deterministic layer sums.
Random geometry masks and local responses have all been removed pathwise;
only the actual clipped matrices and the same three actual density fields
remain, with their exact true-frame clocks and normalized volumes. -/
theorem actual_root_energy_le_layer_sums (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau r)
        (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) k (rootBlockStart Q k))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) ω z ≠ ∞)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) (q : Vec 2) :
    let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
    let w := fun n => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (n-1):ℝ))
    ENNReal.ofReal ((Annealed.sigmaBar M m:ℝ)*dotProduct q ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤
      ENNReal.ofReal (G*rootEdelta r)*
        ((∑' n : ℕ, ENNReal.ofReal (∑ P ∈ whitneyRootLayer Q H n,
          w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal*
            fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P (rootTau r) ω)))+
        ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*
          ∑' n : ℕ, ENNReal.ofReal (w n*(planarGradientCharge 40+1)*
            ((∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
              (layerResolutionDiameter M Q H (rootTau r)
                (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) n e ω x)^2)/
                  (volume (cubeSet Q)).toReal)*dotProduct q q)) := by
  let τ := rootTau r
  let η := ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)
  let S := rootBadWhitneyCells M Q H τ η ω
  let w := fun n : ℕ => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (n-1):ℝ))
  have hw0 (n : ℕ) : 0 ≤ w n := by dsimp only [w]; positivity
  have h333 : 333 ≤ H := (show 333 ≤ rootH0 r by cases r <;> norm_num [rootH0]).trans hH
  obtain ⟨C,hCi,hCb,hCa,henergy⟩ := actual_hybrid_root_energy_split M Q H r hH ω hgood m J hQ hm weights hw
  have hi := hybrid_identity_clipped_sum_le_layers M Q H S τ ω w hw0 q
  have ha := hybrid_active_square_sum_le_layers M Q H h333 τ η ω hgood S (fun _ h => h.1)
    (fun _ h => h.2) hfinite C hCa w hw0 q
  apply (henergy q).trans
  exact mul_le_mul_right (add_le_add hi (mul_le_mul_right ha
    (ENNReal.ofReal (rootResponseEnvelope (6*τ))))) _

end
end ASDExplicitGamma.Inverse
