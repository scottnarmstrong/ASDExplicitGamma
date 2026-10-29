module

public import ASDExplicitGamma.Inverse.RootLayerEnergy
public import ASDExplicitGamma.Inverse.LayerObservables

/-! The actual root comparison written in the exact positive-series indices. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The physical hybrid layer bound has precisely the k>=1 and h>=H0
indices of the source positive series, including its empty zeroth layer. -/
theorem actual_root_energy_le_clocked_observables (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (r : RootRow) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau r)
        (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) k (rootBlockStart Q k))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r))) ω z ≠ ∞)
    (m J : ℤ) (hQ : Q.scale ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1) (q : Vec 2) (hq : dotProduct q q=1) :
    let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
    let w := fun k => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℝ))
    ENNReal.ofReal ((Annealed.sigmaBar M m:ℝ)*dotProduct q ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤
      ENNReal.ofReal G*(ENNReal.ofReal (rootEdelta r)*∑' k : ℕ,
        (ENNReal.ofReal (w k*rootLayerClippedQuadratic M Q r (H-rootH0 r,k) ω q)+
          ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*
            ENNReal.ofReal (w k*(planarGradientCharge 40+1)*rootLayerDensityAverage M Q r (H-rootH0 r,k) ω))) := by
  let G := (3:ℝ)^(2*M.gamma*|(m-Q.scale+1:ℤ)|)
  let w := fun n : ℕ => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) (n-1):ℝ))
  let I := fun n : ℕ => ∑ P ∈ whitneyRootLayer Q H n,
    w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal*
      fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P (rootTau r) ω)
  let D := fun n : ℕ => w n*(planarGradientCharge 40+1)*
    ((∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
      (layerResolutionDiameter M Q H (rootTau r)
        (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) n e ω x)^2)/(volume (cubeSet Q)).toReal)*dotProduct q q
  have hI0 : I 0=0 := by simp only [I,root_whitney_layer_zero,Finset.sum_empty]
  have hD0 : D 0=0 := by simp only [D,root_layer_carrier_zero,Measure.restrict_empty,
    integral_zero_measure,Finset.sum_const_zero,zero_div,mul_zero,zero_mul]
  have hI (k : ℕ) : I (k+1)=w (k+1)*rootLayerClippedQuadratic M Q r (H-rootH0 r,k) ω q := by
    change (∑ P ∈ whitneyRootLayer Q H (k+1), _)=w (k+1)*
      ∑ P ∈ whitneyRootLayer Q (rootH0 r+(H-rootH0 r)) (k+1), _
    rw [Nat.add_sub_of_le hH,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    ring
  have hD (k : ℕ) : D (k+1)=w (k+1)*(planarGradientCharge 40+1)*
      rootLayerDensityAverage M Q r (H-rootH0 r,k) ω := by
    dsimp only [D,rootLayerDensityAverage,Prod.fst,Prod.snd]
    rw [Nat.add_sub_of_le hH,hq,mul_one]
  have hroot := actual_root_energy_le_layer_sums M Q H r hH ω hgood hfinite m J hQ hm weights hw q
  change ENNReal.ofReal _ ≤ ENNReal.ofReal (G*rootEdelta r)*
    ((∑' n, ENNReal.ofReal (I n))+ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*
      ∑' n, ENNReal.ofReal (D n)) at hroot
  have hinside : ((∑' n, ENNReal.ofReal (I n))+ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*
      ∑' n, ENNReal.ofReal (D n))=
      ∑' k : ℕ, (ENNReal.ofReal (w (k+1)*rootLayerClippedQuadratic M Q r (H-rootH0 r,k) ω q)+
        ENNReal.ofReal (rootResponseEnvelope (6*rootTau r))*ENNReal.ofReal
          (w (k+1)*(planarGradientCharge 40+1)*rootLayerDensityAverage M Q r (H-rootH0 r,k) ω)) := by
    rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_add,tsum_eq_zero_add' ENNReal.summable,hI0,hD0,
      ENNReal.ofReal_zero,mul_zero,zero_add,zero_add]
    apply tsum_congr
    intro k
    rw [hI,hD]
  rw [hinside,ENNReal.ofReal_mul (show 0 ≤ G by dsimp only [G]; positivity),mul_assoc] at hroot
  simpa only [w,Nat.add_sub_cancel] using hroot

end
end ASDExplicitGamma.Inverse
