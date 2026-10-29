module

public import ASDExplicitGamma.Inverse.StoppedKuhnGlobalBadCells
public import ASDExplicitGamma.Inverse.StoppedKuhnGlobalIdentityCells
public import ASDExplicitGamma.Inverse.StoppedKuhnLoadCoordinates
public import ASDExplicitGamma.Inverse.StoppedKuhnActiveCharge
public import ASDExplicitGamma.Inverse.StoppedKuhnFinalFields
public import ASDExplicitGamma.Inverse.StoppedPastDiameterFinite
public import ASDExplicitGamma.Inverse.StoppedKuhnFlux

/-! Source planar geometry on the actual q3 law. The single loading-independent
Kuhn midpoint map has finite H1 energy, exact bad/identity behavior, constant
final-simplex gradients and the literal three-resolution active charge. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

local instance planarMidpointGeometryFiniteVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual q3/native-past geometry adapter. No stopped-chain, component,
node, compatibility, finite-energy or diameter-finiteness premise remains. -/
theorem q3_planar_midpoint_geometry (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState M h k) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let H := q3StoppedHeight M Q H0 τ (waveGateEta t) ω
      let η := waveGateEta t
      let S := rootBadWhitneyCells M Q H τ η ω
      ∃ (Phi : Fin 2 → H1Function (openCubeSet Q))
          (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)),
        (∀ i, MemH10 (openCubeSet Q) (Phi i-diagAffineLinear Q (basisVec i)).toFun) ∧
        (∀ (p : Vec 2) (r : H10Function (openCubeSet Q)),
          I (ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r)=
            ∑ i : Fin 2, p i • Phi i) ∧
        (∀ (p : Vec 2) (r : H10Function (openCubeSet Q)),
          MemH10 (openCubeSet Q)
            (ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r-
              I (ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun) ∧
        (∀ V ∈ S, ∃ c : Vec 2, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
          x ∈ openCubeSet V → (∀ i, (Phi i).toFun x=c i) ∧ ∀ i k, (Phi i).grad x k=0) ∧
        (∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
          P ∈ whitneyRootLayer Q H n → (∀ V ∈ S, ¬ CubeTouch P V) → x ∈ openCubeSet P →
            (∀ i, (Phi i).toFun x=x i) ∧ ∀ i k, (Phi i).grad x k=basisVec i k) ∧
        (∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
          P ∈ whitneyRootLayer Q H n → x ∈ openCubeSet P →
            ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (fun i k => (Phi k).grad x i)‖^2 ≤
              1+planarGradientCharge 40*(∑ e : Fin 3, (layerResolutionDiameter M Q H τ η n e ω x)^2)) ∧
        (∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), ∀ (n : ℕ) (P : TriadicCube 2),
          P ∈ whitneyRootLayer Q H n → (∃ V ∈ S, CubeTouch P V) → x ∈ openCubeSet P →
            ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (fun i k => (Phi k).grad x i)‖^2 ≤
              (planarGradientCharge 40+1)*(∑ e : Fin 3, (layerResolutionDiameter M Q H τ η n e ω x)^2)) ∧
        (∀ (n : ℕ) (P : TriadicCube 2), P ∈ whitneyRootLayer Q H n →
          ∀ U ∈ finalWhitneyKuhnCells Q H n P, ∃ F : Matrix (Fin 2) (Fin 2) ℝ,
            ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ U.openCarrier → (fun i k => (Phi k).grad x i)=F) ∧
        (∀ q : Vec 2,
          MemVectorL2 (openCubeSet Q)
            (fun x => matVecMul (planarFluxMatrix (fun i k => (Phi k).grad x i)) q-q) ∧
          IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
            (fun x => matVecMul (planarFluxMatrix (fun i k => (Phi k).grad x i)) q-q)) := by
  have hgood := q3_stopped_height_ae_good M h hM hg Q H0 hH0 τ hτ t q hq0 hq hraw hpast
  have hfin := q3_past_diameter_ae_ne_top M h hM hg (Q.scale-(H0:ℤ)) τ hτ t q hq0 hq hraw
    (fun k hk => hpast k (by omega))
  filter_upwards [hgood,hfin] with ω hωg hωf
  let H := q3StoppedHeight M Q H0 τ (waveGateEta t) ω
  let S := rootBadWhitneyCells M Q H τ (waveGateEta t) ω
  have hHH0 : H0 ≤ H := q3_stopped_height_ge M Q H0 τ (waveGateEta t) ω
  have hH : 333 ≤ H := hH0.trans hHH0
  have hS : S ⊆ whitneyRootPartition Q H := fun _ hV => hV.1
  have hbad : ∀ V ∈ S, ω ∈ cellFailure M τ (waveGateEta t) V := fun _ hV => hV.2
  have hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j τ (waveGateEta t)) ω z ≠ ∞ := by
    intro j hj z
    exact hωf j (by omega) z
  let Phi := stoppedKuhnMidpointCoordinate M Q H hH τ (waveGateEta t) ω hωg S hS hbad
  let I := stoppedKuhnMidpointLinearInterpolant M Q H hH τ (waveGateEta t) ω hωg S hS hbad
  dsimp only
  refine ⟨Phi,I,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact stopped_kuhn_coordinate_residual_memH10 M Q H hH τ (waveGateEta t) ω hωg S hS hbad
  · exact stopped_kuhn_interpolant_affine_coordinates M Q H hH τ (waveGateEta t) ω hωg S hS hbad
  · exact stopped_kuhn_midpoint_interpolant_residual_memH10 M Q H hH τ (waveGateEta t) ω hωg S hS hbad
  · intro V hVS
    refine ⟨stoppedCanonicalMidpoint M Q H hH τ (waveGateEta t) ω hωg S hS hbad V hVS,?_⟩
    have hb := ae_all_iff.mpr (fun i : Fin 2 =>
      stopped_global_kuhn_midpoint_ae_bad_cells M Q H hH τ (waveGateEta t) ω hωg S hS hbad i)
    filter_upwards [hb] with x hx
    intro hxV
    exact ⟨fun i => (hx i V hVS hxV).1,fun i k => (hx i V hVS hxV).2 k⟩
  · have hi := ae_all_iff.mpr (fun i : Fin 2 =>
      stopped_global_kuhn_midpoint_ae_identity_cells M Q H hH τ (waveGateEta t) ω hωg S hS hbad i)
    filter_upwards [hi] with x hx
    intro n P hP hoff hxP
    exact ⟨fun i => (hx i n P hP hoff hxP).1,fun i k => (hx i n P hP hoff hxP).2 k⟩
  · exact stopped_kuhn_gradient_ae_three_resolution_charge M Q H hH τ (waveGateEta t) ω hωg S hS hbad hfinite
  · exact stopped_kuhn_gradient_ae_active_charge M Q H hH τ (waveGateEta t) ω hωg S hS hbad hfinite
  · intro n P hP U hU
    exact stopped_kuhn_gradient_constant_on_final_simplex M Q H hH τ (waveGateEta t) ω hωg S hS hbad n P hP U hU

  · exact stopped_kuhn_flux_admissible M Q H hH τ (waveGateEta t) ω hωg S hS hbad

end
end ASDExplicitGamma.Inverse
