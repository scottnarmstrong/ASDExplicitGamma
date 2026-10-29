module

public import ASDExplicitGamma.Native.OldSignedAveragePairing
public import ASDExplicitGamma.Native.OldSignedLocalData
public import ASDExplicitGamma.Main.InverseLowerRowBound
public import ASDExplicitGamma.Scalar.DualEnergy

/-! Qualitative first-gradient control by the true physical energy.
This is used only to prove convergence of the actual projected families. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- Every actual L2 doubled field has first weak-Haar norm controlled by
its physical energy. No coarse-history estimate is needed for this
qualitative convergence bound. -/
theorem old_signed_first_weak_le_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (A : Vec 2 → BlockVec 2) (hA : MemBlockL2 (openCubeSet Q) A) :
    vectorWeakHaarNorm Q (fun x => (A x).1)^2≤
      (sigma/nu)*oldSignedEnergyPairing Q nu sigma k A A := by
  have hfirst := memVectorL2_fst_of_memBlockL2 hA
  have havg := old_signed_vector_average_pairing Q (fun x => (A x).1) (fun x => (A x).1) hfirst hfirst
  change volumeAverage (openCubeSet Q) (fun x => vecNormSq (A x).1)=
    ∑ i : Fin 2,energy Q (fun x => (A x).1 i) at havg
  have hpoint (x : Vec 2) : (nu/sigma)*vecNormSq (A x).1≤
      responseFrameEnergyDensity nu sigma (responseCoefficientExtension k x) (A x) := by
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hsigma.le hnu.le) (vecNormSq_nonneg _))
  have hi := integral_mono_ae
    ((integrableOn_vecDot_of_memVectorL2 hfirst hfirst).const_mul (nu/sigma))
    (scalar_field_density_integrable Q nu sigma hnu hsigma k hA)
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hi
  have hn := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (ENNReal.toReal_nonneg : 0≤(volume (openCubeSet Q)).toReal))
  have he : (nu/sigma)*(∑ i : Fin 2,energy Q (fun x => (A x).1 i))≤scalarFieldEnergy nu sigma k A := by
    rw [←havg]
    unfold scalarFieldEnergy volumeAverage vecNormSq
    convert hn using 1
    ring
  have hE : scalarFieldEnergy nu sigma k A=oldSignedEnergyPairing Q nu sigma k A A := by
    unfold scalarFieldEnergy oldSignedEnergyPairing
    congr 1
    funext x
    exact responseFrameEnergyDensity_eq_scaledCoefficientBlock nu sigma (responseCoefficientExtension k x) hnu hsigma (A x)
  rw [hE] at he
  have hw : vectorWeakHaarNorm Q (fun x => (A x).1)^2≤
      ∑ i : Fin 2,energy Q (fun x => (A x).1 i) := by
    rw [vectorWeakHaarNorm,Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)]
    exact main_vectorWeakHaarEnergy_le_coordinateEnergy Q _
      (fun i => memLp_normalized_of_memL2On (hfirst.eval i))
  have hh := (mul_le_mul_of_nonneg_left hw (div_nonneg hnu.le hsigma.le)).trans he
  calc
    _ = (sigma/nu)*((nu/sigma)*vectorWeakHaarNorm Q (fun x => (A x).1)^2) := by
      field_simp [hnu.ne',hsigma.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (div_nonneg hsigma.le hnu.le)

end
end ASDExplicitGamma.Native
