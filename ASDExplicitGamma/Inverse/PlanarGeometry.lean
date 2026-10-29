module

public import ASDExplicitGamma.Inverse.PlanarMidpointGeometry
public import ASDExplicitGamma.Inverse.WhitneyLayerWeights

/-! The source IN-PLANAR-GEOMETRY adapter: actual-law stopped tail, exact
physical Whitney fractions, depth-two final mesh and one common finite-energy
midpoint map. All statistical inputs come from the model and protected past. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

local instance planarGeometryFiniteVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Complete source planar geometry at a fixed entrance and true-frame gate
tuple. In particular the local bad-event and positive-label Gaussian bounds
are consumed internally, rather than assumed as estimates. -/
theorem q3_planar_geometry (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState M h k) :
    let K := q3StoppedHeight M Q H0 τ (waveGateEta t)
    Measurable K ∧ (∀ ω, H0 ≤ K ω) ∧
    (∀ k, H0 ≤ k → (Cutoff.cutoffSampleLaw M).toMeasure.real {ω | k < K ω} ≤
      Real.exp (-heightExponent k/32)) ∧
    bankLayerWeight 0=1/9 ∧
    (∀ n, bankLayerWeight (n+1)=8*(1/3:ℝ)^(n+2)-32*(1/9:ℝ)^(n+2)) ∧
    HasSum bankLayerWeight 1 ∧
    (∀ ω n, (volume (rootLayerCarrier Q (K ω) (n+1))).toReal=
      bankLayerWeight n*(volume (cubeSet Q)).toReal) ∧
    (∀ ω n (P : TriadicCube 2), P ∈ whitneyRootLayer Q (K ω) n →
      Q.scale-(compatibleWhitneyMeshDepth (K ω) (n+1):ℤ) ≤ P.scale ∧
      P.scale ≤ Q.scale-(compatibleWhitneyMeshDepth (K ω) (n+1):ℤ)+2) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let H := K ω
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
            (fun x => matVecMul (planarFluxMatrix (fun i k => (Phi k).grad x i)) q-q))) := by
  dsimp only
  refine ⟨q3_stopped_height_measurable M Q H0 τ (waveGateEta t),
    q3_stopped_height_ge M Q H0 τ (waveGateEta t),
    q3_stopped_height_tail M h hM hg Q H0 hH0 τ hτ t q hq0 hq hraw hpast,
    layerWeight_zero,layerWeight_succ,layerWeight_hasSum,?_,?_,?_⟩
  · intro ω n
    exact root_layer_carrier_volume Q _ n
  · intro ω n P hP
    exact final_whitney_kuhn_depth_range Q _ n hP
  · exact q3_planar_midpoint_geometry M h hM hg Q H0 hH0 τ hτ t q hq0 hq hraw hpast

end
end ASDExplicitGamma.Inverse
