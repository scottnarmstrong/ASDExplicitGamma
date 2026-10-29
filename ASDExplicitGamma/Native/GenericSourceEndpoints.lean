module

public import ASDExplicitGamma.Native.GenericSourceShellBudget

/-! Literal compact-field endpoint identities and source-band telescoping. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
noncomputable section

/-- Adding the fresh shell to the completed older field gives the next
completed field, as an equality in the compact continuous-function space. -/
theorem native_source_older_field_succ (K : Set (Vec 2)) [CompactSpace K]
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2) :
    olderField K (m+1) ω = olderField K m ω+
      shellFieldScalarRestriction K (ω.1 (m+1)) := by
  have hs : Summable (fun r : ℕ => shellFieldScalarRestriction K (ω.1 (m+1-(r:ℤ)))) := by
    apply Summable.of_norm_bounded (Cutoff.summable_cutoffLocalControl ell (m+1) ω)
    intro r
    apply (ContinuousMap.norm_le _ (Cutoff.localCubeControl_nonneg ell _)).mpr
    intro x
    rw [Real.norm_eq_abs]
    exact Cutoff.abs_entry_le_localCubeControl ell _ (hK x.2) 1 0
  rw [olderField, hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero,sub_zero]
  rw [add_comm]
  congr 1
  apply tsum_congr
  intro r
  have hi : m+1-((r+1:ℕ):ℤ)=m-(r:ℤ) := by omega
  rw [hi]

/-- Actual insertion endpoints agree with the completed older fields. -/
theorem native_source_inserted_endpoints (K : Set (Vec 2)) [CompactSpace K]
    (ell m : ℤ) (hK : K ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2) :
    modelInsertedScalar K m 0 ω = olderField K m ω ∧
    modelInsertedScalar K m 1 ω = olderField K (m+1) ω := by
  constructor
  · simp only [modelInsertedScalar,Real.sqrt_zero,zero_smul,add_zero]
  · simp only [modelInsertedScalar,Real.sqrt_one,one_smul]
    exact (native_source_older_field_succ K ell m hK ω).symm

/-- The completed-band root in the fixed true frame of the starting label. -/
def nativeSourceBandRoot (M : ABKModel 2) (n : ℤ) (height : ℕ) : ℝ :=
  (∫ ω : Cutoff.CutoffSample 2,
    (modelTraceObservable n M.nu (Annealed.sigmaBar M n)
      (olderField (closure (cubeSet (originCube 2 n))) (n+(height:ℤ)) ω))^(20:ℝ)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure)^((20:ℝ)⁻¹)

end
end ASDExplicitGamma.Native
