module

public import ASDExplicitGamma.Scalar.DefectEnergyCarrierOperators

/-! Actual H10 first-potential inputs for the infinite q3 defect Wick family. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

noncomputable section

/-- Choose the genuine zero-trace first potential carried by one physical
OLD-minus-flat q3 response mode. -/
noncomputable def q3DefectModePotential (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) :
    H10Function (openCubeSet Q) :=
  Classical.choose (q3_defect_response_mode_first_potential Q ν σ hν hσ
    k b L load n)

/-- The selected potential is the actual first component of its physical
response mode, up to volume-null equality. -/
theorem q3DefectModePotential_spec (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) :
    (fun x => (hilbertBlockL2ToBlockL2
      (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x).1) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (q3DefectModePotential Q ν σ hν hσ k b L load n).toH1Function.grad :=
  Classical.choose_spec (q3_defect_response_mode_first_potential Q ν σ hν hσ
    k b L load n)

/-- The first-potential mode embedded in the actual weak-Haar H10 graph. -/
noncomputable def q3DefectModeWeakPotential (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) :
    defectWeakPotential Q :=
  defectWeakPotentialOfH10 Q
    (q3DefectModePotential Q ν σ hν hσ k b L load n)

/-- Each input-carrier norm is bounded by the source's full broken modal
weak-Haar budget. This is the summability bridge from the actual block mode
to the first-potential input consumed by the q3 source operator. -/
theorem q3DefectModeWeakPotential_norm_sq_le (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2) (n : whiteBasisIndex) :
    ‖q3DefectModeWeakPotential Q ν σ hν hσ k b L load n‖ ^ 2 ≤
      q3DefectWeakModeEnergy Q ν σ hν hσ k b L load n := by
  let r := q3DefectModePotential Q ν σ hν hσ k b L load n
  let d := q3DefectModeWeakPotential Q ν σ hν hσ k b L load n
  let G : Vec 2 → Vec 2 := graphPotentialField Q d.down
  let F : Vec 2 → Vec 2 := fun x =>
    (hilbertBlockL2ToBlockL2
      (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x).1
  have hblock : MemBlockL2 (openCubeSet Q) (fun x =>
      hilbertBlockL2ToBlockL2
        (q3DefectResponseMode Q ν σ hν hσ k b L load n).down x) :=
    MeasureTheory.Lp.memLp _
  have hFvec : MemVectorL2 (openCubeSet Q) F := by
    exact memVectorL2_fst_of_memBlockL2 hblock
  have hGvec : MemVectorL2 (openCubeSet Q) G := MeasureTheory.Lp.memLp _
  have hFmem : ∀ i : Fin 2,
      MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hGmem : ∀ i : Fin 2,
      MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hGvec i)
  have hrmem : ∀ i : Fin 2,
      MemLp (fun x => r.toH1Function.grad x i) 2 (normalizedCubeMeasure Q) :=
    fun i => r.toH1Function.grad_memL2_normalizedCubeMeasure i
  have hmeasure : cubeMeasure Q = volumeMeasureOn (openCubeSet Q) := by
    rw [cubeMeasure, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hFGvol : F =ᵐ[cubeMeasure Q] r.toH1Function.grad := by
    rw [hmeasure]
    simpa [F, r] using
      q3DefectModePotential_spec Q ν σ hν hσ k b L load n
  have hFG : F =ᵐ[normalizedCubeMeasure Q] r.toH1Function.grad := by
    rw [normalizedCubeMeasure]
    exact Measure.ae_smul_measure hFGvol (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  have hGr : G =ᵐ[normalizedCubeMeasure Q] r.toH1Function.grad := by
    simpa [G, d, q3DefectModeWeakPotential] using
      graphPotentialField_ofH10_normalized Q r
  have hnorm : ‖d‖ ^ 2 = vectorWeakHaarEnergy Q
      (r.toH1Function.grad) := by
    rw [defectWeakPotential_norm_sq]
    exact vectorWeakHaarEnergy_congr_ae Q hGmem hrmem hGr
  have hweak : vectorWeakHaarEnergy Q (r.toH1Function.grad) ≤
      q3DefectWeakModeEnergy Q ν σ hν hσ k b L load n := by
    have heq := vectorWeakHaarEnergy_congr_ae Q hrmem hFmem hFG.symm
    rw [heq]
    exact q3_defect_first_weak_energy_le_mode_energy Q ν σ hν hσ k b L load n
  simpa [d] using hnorm.trans_le hweak

/-- The physical two-index OLD-minus-flat shear mode is exactly the common
q3 projected-source operator applied to the chosen first-potential carrier.
This is the bilinear identity consumed by the infinite Gaussian
passage. -/
theorem q3DefectShearMode_eq_weakPotential_operator (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (load : Fin 2)
    (i j : whiteBasisIndex) :
    let hU := measurableSet_openCubeSet Q
    let hvol := by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q
    let D := responseFrameEnergyData hU hvol ν σ hν hσ k
    let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
    V.toSubmoduleᗮ.starProjection
      (q3DefectShearMode Q ν σ hν hσ k b L load i j) =
    defectPotentialSourceComplementLinear Q ν σ hν hσ k b L i
      (q3DefectModeWeakPotential Q ν σ hν hσ k b L load j) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let d := q3DefectModeWeakPotential Q ν σ hν hσ k b L load j
  let r := defectWeakPotentialRepresentative Q d
  let Hleft := σ • mainShellResponseCoefficient Q b L (whiteBasis i)
  let Hright := σ • mainShellResponseCoefficient Q b L (whiteBasis j)
  let η := mainQ3DirectionW2 Q b L (whiteBasis i)
  have hgrad : r.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (q3DefectModePotential Q ν σ hν hσ k b L load j).toH1Function.grad := by
    have hrep := graphPotentialField_ofRepresentative Q d
    have hmode := graphPotentialField_ofH10 Q
      (q3DefectModePotential Q ν σ hν hσ k b L load j)
    exact hrep.symm.trans (by simpa [d, q3DefectModeWeakPotential] using hmode)
  have hfirst : (fun x => (hilbertBlockL2ToBlockL2
      (q3DefectResponseMode Q ν σ hν hσ k b L load j).down x).1) =ᵐ[
        volumeMeasureOn (openCubeSet Q)] r.toH1Function.grad := by
    exact (q3DefectModePotential_spec Q ν σ hν hσ k b L load j).trans hgrad.symm
  have hlink : η.value.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => responseCoefficientExtension Hleft x / σ := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)]
      with x hx
    change q3Convolution b L h3Zero (whiteBasis i) x =
      responseCoefficientExtension Hleft x / σ
    rw [responseCoefficientExtension_smul_on σ _ hx,
      mainShellResponseCoefficient_extension Q b L (whiteBasis i) hx]
    field_simp [hσ.ne']
  have hprojection := second_defect_source_projection_eq Q ν σ hν hσ k
    (basisVec load, 0) Hleft Hright
    (-flatPureFluxMode Q b L j load) r η hlink hfirst
  have hF : MemLp (defectPotentialSourceFieldCarrier Q b L i d) 2
      (normalizedCubeMeasure Q) :=
    defectPotentialSourceFieldCarrier_memLp Q b L i d
  have hsource : defectPotentialSourceFieldCarrier Q b L i d =
      planarShearSourceField (diagInterpolant Q 0) η r.toH1Function := by
    rfl
  change V.toSubmoduleᗮ.starProjection
      (q3DefectShearMode Q ν σ hν hσ k b L load i j) = _
  calc
    _ = V.toSubmoduleᗮ.starProjection
        (responseEnergyUp D (projectedSourceLoad Q hF)) := by
      simpa [q3DefectShearMode, d, r, Hleft, Hright, hsource] using hprojection
    _ = responseEnergyUp D
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)) := by
      exact projectedSource_carrier_complement_eq Q hU hvol ν σ hν hσ k hF
    _ = defectPotentialSourceComplementLinear Q ν σ hν hσ k b L i d := by
      symm
      exact defectPotentialSourceComplementLinear_apply Q ν σ hν hσ k b L i d

end
end ASDExplicitGamma.Scalar
