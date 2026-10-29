module

public import ASDExplicitGamma.Variational.LocalizedShearMinimum
public import ASDExplicitGamma.Variational.LocalizedEnergyOperator

/-! Assembly of the localized shear and its fixed-energy operator. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

local instance localizedShearBundleFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual-space localized shear package: weak cancellation, a genuine
fixed-load affine automorphism, the literal row, nilpotence and its exact
energy norm bound, and equality of the actual energy infima. -/
theorem localizedShear_source_bundle (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict (openCubeSet Q)))
    (hres : ∀ r : H10Function (openCubeSet Q), MemH10 (openCubeSet Q)
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r-I
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 r)).toFun)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q,
      ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖)
    (hR : ∀ v ∈ affinePotentialSubmodule Q,
      ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖)
    (ε : ℝ) :
    (∀ r : H10Function (openCubeSet Q),
      MemVectorL2 (openCubeSet Q)
        (localizedColumnProductDivergence η r.toH1Function) ∧
      IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
        (localizedColumnProductDivergence η r.toH1Function)) ∧
    Nonempty (LocalizedAdmissibleState (openCubeSet Q) P ≃
      LocalizedAdmissibleState (openCubeSet Q) P) ∧
    (∀ Z : LocalizedAdmissibleState (openCubeSet Q) P, ∀ x,
      responseShear σ (ε*η.toFun x)
          ((localizedAdmissibleShear (isOpenBoundedConvexDomain_openCubeSet Q)
            P I η hη hDη hres ε σ Z).field.eval x) =
        ((lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 Z.correction).grad x,
          Z.flux x-(ε/σ) • lemmaVPlanarRowField I η
            (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) P.1 Z.correction) x)) ∧
    (∀ R S : affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q),
      (localizedEnergyOperator Q
        (responseFrameEnergyData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k) σ R).comp
        (localizedEnergyOperator Q
          (responseFrameEnergyData (measurableSet_openCubeSet Q)
            (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
            ν σ hν hσ k) σ S) = 0) ∧
    (‖localizedEnergyOperator Q
        (responseFrameEnergyData (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν σ hν hσ k) σ
        (localizedRowOperator Q I η hη hDη hA hB hI hR)‖ ≤
      (A*‖hη.toLp η.toFun‖+B*‖weakColumnDivergenceLp η hDη‖)/ν) ∧
    (∀ Z : LocalizedAdmissibleState (openCubeSet Q) P, ∀ x,
      responseFrameEnergyDensity ν σ
          (responseCoefficientExtension k x+ε*η.toFun x)
          ((localizedAdmissibleShear (isOpenBoundedConvexDomain_openCubeSet Q)
            P I η hη hDη hres ε σ Z).field.eval x) =
        responseFrameEnergyDensity ν σ (responseCoefficientExtension k x)
          ((localizedPerturbedField (isOpenBoundedConvexDomain_openCubeSet Q)
            P I η ε σ Z).eval x)) ∧
    (sInf {e : ℝ | ∃ X : BlockState 2, IsBlockMuAdmissible (openCubeSet Q) P X ∧
      e = volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity ν σ
        (responseCoefficientExtension k x+ε*η.toFun x) (X.eval x))} =
      sInf (Set.range (fun Z : LocalizedAdmissibleState (openCubeSet Q) P =>
        volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity ν σ
          (responseCoefficientExtension k x)
          ((localizedPerturbedField (isOpenBoundedConvexDomain_openCubeSet Q)
            P I η ε σ Z).eval x))))) := by
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  have hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ⟨localizedColumnProductDivergence_memL2 η r.toH1Function hη hDη,
      localizedColumnProductDivergence_solenoidal hU η r.toH1Function r.memH10 hη hDη⟩
  · exact ⟨localizedAdmissibleShearEquiv hU P I η hη hDη hres ε σ⟩
  · intro Z x
    exact localizedAdmissibleShear_composition hU P I η hη hDη hres ε σ Z x
  · intro R S
    exact localizedEnergyOperator_pairwise_nilpotent Q
      (responseFrameEnergyData (measurableSet_openCubeSet Q) hvol ν σ hν hσ k) σ R S
  · exact localizedEnergyOperator_row_norm_le Q (measurableSet_openCubeSet Q) hvol
      ν σ hν hσ k I η hη hDη hA hB hI hR
  · intro Z x
    exact localizedShear_energy_identity hU P I η hη hDη hres ν ε σ
      (responseCoefficientExtension k) Z x
  · exact localizedShear_response_minimum hU P I η hη hDη hres ν ε σ
      (responseCoefficientExtension k)

end
end ASDExplicitGamma.Variational
