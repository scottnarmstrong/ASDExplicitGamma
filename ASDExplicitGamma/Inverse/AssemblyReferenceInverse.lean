module

public import ASDExplicitGamma.Inverse.AssemblyReferenceEnergy
public import ASDExplicitGamma.Inverse.AssemblyLayerSums
public import ASDExplicitGamma.Inverse.AssemblyPositiveSeries

/-! Actual inverse assembly in its source root frame. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The complete root energy is paid by deterministic clipped-matrix
layers and the three actual geometric density fields. -/
theorem assembly_root_framed_energy_le_layers (M : ABKModel 2)
    (Q : TriadicCube 2) (k H : ℕ) (hH : heightEntrance k ≤ H)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) resetAllOrderTau (waveGateEta .allOrder))
      j (rootBlockStart Q j))
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)) ω z ≠ ∞)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale k) N,
      0 ≤ weights n ∧ weights n ≤ 1) (q : Vec 2) :
    let w := fun n : ℕ => rootAssemblyClock M.gamma H n
    ENNReal.ofReal ((Annealed.sigmaBar M (Q.scale-1):ℝ) *
      dotProduct q ((coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M (protectedOldLabel Q.scale k) N weights ω)).lowerRight.mulVec q)) ≤
      ENNReal.ofReal rootAssemblySensitivity *
        ((∑' n : ℕ, ENNReal.ofReal (∑ P ∈ whitneyRootLayer Q H n,
          w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal *
            fullMatrixQuadratic (toFullBlockVec (0,q))
              (clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω))) +
          ENNReal.ofReal (rootResponseEnvelope (6*resetAllOrderTau)) *
            ∑' n : ℕ, ENNReal.ofReal (w n*(planarGradientCharge 40+1) *
              ((∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
                (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder)
                  n e ω x)^2)/(volume (cubeSet Q)).toReal) * dotProduct q q)) := by
  let τ := resetAllOrderTau
  let η := waveGateEta .allOrder
  let S := rootBadWhitneyCells M Q H τ η ω
  let w := fun n : ℕ => rootAssemblyClock M.gamma H n
  have hw0 (n : ℕ) : 0 ≤ w n := (root_assembly_clock_pos M.gamma H n).le
  have h333 : 333 ≤ H := by
    unfold heightEntrance at hH
    omega
  obtain ⟨C,hCi,hCb,hCa,henergy⟩ :=
    assembly_hybrid_root_framed_split M Q k H hH ω hgood N hN weights hw
  have hi := hybrid_identity_clipped_sum_le_layers M Q H S τ ω w hw0 q
  have ha := hybrid_active_square_sum_le_layers M Q H h333 τ η ω hgood S
    (fun _ h => h.1) (fun _ h => h.2) hfinite C hCa w hw0 q
  apply (henergy q).trans
  exact mul_le_mul_right (add_le_add hi (mul_le_mul_right ha
    (ENNReal.ofReal (rootResponseEnvelope (6*τ))))) _

/-- The geometry supplies the actual finite-energy comparison
almost surely. The geometric partition height is the full stopping index;
its source layer-height index is five less. -/
theorem assembly_q3_root_framed_energy_le_majorant (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ q : Vec 2,
      ENNReal.ofReal ((Annealed.sigmaBar M (Q.scale-1):ℝ) *
          dotProduct q ((coarseBlockMatrix (cubeSet Q)
            (attenuatedCoefficient M (protectedOldLabel Q.scale (orderBand p))
              N weights ω)).lowerRight.mulVec q)) ≤
        assemblyInverseLayerMajorant M Q
          (resetQ3StoppedHeight M Q (orderBand p) ω) ω q := by
  let H0 := heightEntrance (orderBand p)+5
  have hH0 : 333 ≤ H0 := by unfold H0 heightEntrance; omega
  have hτ : 0 < resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hq0 : 0 ≤ (allOrderDensity:ℝ) :=
    ((Real.exp_pos _).trans all_order_density_floor).le
  have hprotected : ∀ n ≤ Q.scale-(H0:ℤ)+40, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    unfold H0 heightEntrance at hn
    omega
  have hgeometry := reset_q3_planar_geometry M h hM hγ Q p hp hpast
  have hgood := q3_stopped_height_ae_good M h hM hγ Q H0 hH0
    resetAllOrderTau hτ .allOrder (allOrderDensity:ℝ) hq0
    all_order_density_small all_order_density_covers_raw hprotected
  have hfin := q3_past_diameter_ae_ne_top M h hM hγ (Q.scale-(H0:ℤ))
    resetAllOrderTau hτ .allOrder (allOrderDensity:ℝ) hq0
    all_order_density_small all_order_density_covers_raw
    (fun n hn => hprotected n (by omega))
  filter_upwards [hgood,hfin] with ω hωg hωf
  intro q
  let H := resetQ3StoppedHeight M Q (orderBand p) ω
  have hHH0 : H0 ≤ H := hgeometry.2.1 ω
  have hH : heightEntrance (orderBand p) ≤ H := by
    dsimp only [H0] at hHH0
    omega
  have hsuccess : ∀ j, H ≤ j → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-j) resetAllOrderTau (waveGateEta .allOrder))
      j (rootBlockStart Q j) := hωg
  have hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)) ω z ≠ ∞ := by
    intro j hj z
    exact hωf j (by omega) z
  exact assembly_root_framed_energy_le_layers M Q (orderBand p) H hH ω
    hsuccess hfinite N hN weights hw q

/-- Uniform unit-energy bounds for the actual target imply the literal
root inverse operator norm bound. Positivity, symmetry and the true-frame
identification are proved internally from the genuine Book coefficient. -/
theorem assembly_inverse_norm_le_of_unit_energies (M : ABKModel 2) (Q : TriadicCube 2)
    (m J ref : ℤ) (hm : m ≤ J) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (B : ℝ≥0∞)
    (hcap : ∀ q : Vec 2, dotProduct q q=1 → ENNReal.ofReal
      ((Annealed.sigmaBar M ref:ℝ)*dotProduct q ((coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec q)) ≤ B) :
    ENNReal.ofReal (rootInverseObservable M Q m J ref weights ω) ≤ B := by
  let A := coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)
  let σ := (Annealed.sigmaBar M ref:ℝ)
  let C := σ • A.lowerRight
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M ref).1
  have he := attenuated_sensitivity_matrix_eq M Q m m J le_rfl hm weights ω
  have hsym : IsSymmetricBlockMat A := by
    change IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω))
    rw [← he]
    exact Book.Ch02.isSymmetricBlockMat_coarseBlockMatrix _ _
  have hHerm : C.IsHermitian := by
    ext i j
    have hh := hsym (Sum.inr j) (Sum.inr i)
    change A.lowerRight j i=A.lowerRight i j at hh
    simp only [C,Matrix.conjTranspose_apply,Matrix.smul_apply,smul_eq_mul,star_trivial]
    rw [hh]
  have hq (q : Vec 2) : dotProduct q (C.mulVec q)=σ*dotProduct q (A.lowerRight.mulVec q) := by
    simp only [C,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  have hpos (q : Vec 2) : 0 ≤ dotProduct q (C.mulVec q) := by
    rw [hq]
    have hh := book_pure_flux_nonneg (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q M.nu M.nu_pos (oldResponseCoefficient Q m ω+
        laterResponseCoefficient Q m J (sourceBandWeights m weights) ω)) q
    rw [he] at hh
    exact mul_nonneg hσ.le hh
  have hh := symmetric_norm_of_unit_extended_bound C hHerm hpos B (by
    intro q hunit
    rw [hq]
    exact hcap q hunit)
  have hn : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) C‖=rootInverseObservable M Q m J ref weights ω := by
    rw [show C=σ • A.lowerRight from rfl,map_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hσ]
    rfl
  rwa [hn] at hh

/-- Actual-law positive inverse assembly: all geometry and local response
premises are discharged from the source model and protected native past. -/
theorem assembly_q3_root_framed_inverse_bound (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (rootInverseObservable M Q
        (protectedOldLabel Q.scale (orderBand p)) N (Q.scale-1) weights ω) ≤
        ENNReal.ofReal (assemblyInverseLi M.gamma) *
          ENNReal.ofReal ((3:ℝ)^(2*M.gamma*
            ((resetQ3StoppedHeight M Q (orderBand p) ω:ℝ)-38))) +
              assemblyInverseError M Q (heightEntrance (orderBand p)+5) ω := by
  have henergy := assembly_q3_root_framed_energy_le_majorant M h hM hγ Q p hp hpast N hN weights hw
  have hgeometry := reset_q3_planar_geometry M h hM hγ Q p hp hpast
  filter_upwards [henergy] with ω hω
  apply assembly_inverse_norm_le_of_unit_energies M Q
    (protectedOldLabel Q.scale (orderBand p)) N (Q.scale-1) (by
      unfold protectedOldLabel
      omega) weights ω
  intro q hq
  exact (hω q).trans (assembly_inverse_majorant_le_positive M h hγ Q
    (orderBand p) (heightEntrance (orderBand p)+5)
    (resetQ3StoppedHeight M Q (orderBand p) ω) le_rfl (hgeometry.2.1 ω) hpast ω q hq)

end
end ASDExplicitGamma.Inverse
