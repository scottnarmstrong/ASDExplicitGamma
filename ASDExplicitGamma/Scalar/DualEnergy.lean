module

public import ASDExplicitGamma.Scalar.DualSpaces

/-! Literal normalized field energy and integrated self-dual Fenchel bound. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory

/-- The actual source energy in the common physical comparison frame. -/
noncomputable def scalarFieldEnergy {U : Set (Vec 2)} (ν σ : ℝ) (k : ResponseCoefficient U)
    (F : Vec 2 → BlockVec 2) : ℝ :=
  volumeAverage U (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (F x))

/-- Admissible L2 fields have finite genuine source energy; no energy-integrability premise is needed. -/
theorem scalar_field_density_integrable (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    IntegrableOn (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (F x))
      (openCubeSet Q) := by
  let state : BlockState 2 := ⟨fun x => (F x).1,fun x => (F x).2⟩
  let instFiniteScalarEnergy : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hs : MemBlockL2 (openCubeSet Q) state.eval := hF
  have hi := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hs hs
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k)
  convert hi using 1
  funext x
  exact responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ (responseCoefficientExtension k x) hν hσ (F x)

/-- Source energy is a genuine quadratic form under scalar multiplication. -/
theorem scalar_field_energy_smul {U : Set (Vec 2)} (ν σ : ℝ) (k : ResponseCoefficient U)
    (F : Vec 2 → BlockVec 2) (t : ℝ) :
    scalarFieldEnergy ν σ k (t • F)=t^2*scalarFieldEnergy ν σ k F := by
  have he : (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) ((t • F) x))=
      t^2 • (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (F x)) := by
    funext x
    simp [responseFrameEnergyDensity,vecNormSq,vecDot,matVecMul,responsePlanarJ,Fin.sum_univ_two]
    ring
  unfold scalarFieldEnergy
  rw [he,volumeAverage_smul]

/-- The literal integrated convex-duality inequality in the true physical frame. -/
theorem scalar_field_fenchel (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {X Z : Vec 2 → BlockVec 2}
    (hX : MemBlockL2 (openCubeSet Q) X) (hZ : MemBlockL2 (openCubeSet Q) Z) :
    2*volumeAverage (openCubeSet Q) (fun x => blockVecDot (scalarBlockExchange (X x)) (Z x))-
      scalarFieldEnergy ν σ k Z ≤ scalarFieldEnergy ν σ k X := by
  have hi1 := integrableOn_vecDot_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hX)
    (memVectorL2_fst_of_memBlockL2 hZ)
  have hi2 := integrableOn_vecDot_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hX)
    (memVectorL2_snd_of_memBlockL2 hZ)
  have hic : IntegrableOn (fun x => blockVecDot (scalarBlockExchange (X x)) (Z x)) (openCubeSet Q) := hi1.add hi2
  have hiZ := scalar_field_density_integrable Q ν σ hν hσ k hZ
  have hiX := scalar_field_density_integrable Q ν σ hν hσ k hX
  have hle := integral_mono ((hic.const_mul 2).sub hiZ) hiX
    (fun x => scalar_block_fenchel ν σ (responseCoefficientExtension k x) hν hσ (X x) (Z x))
  unfold scalarFieldEnergy volumeAverage
  simp only [Pi.sub_apply] at hle
  rw [integral_sub (hic.const_mul 2) hiZ,integral_const_mul] at hle
  have h := mul_le_mul_of_nonneg_left hle
    (inv_nonneg.mpr (ENNReal.toReal_nonneg : 0 ≤ (volume (openCubeSet Q)).toReal))
  nlinarith only [h]

end ASDExplicitGamma.Scalar
