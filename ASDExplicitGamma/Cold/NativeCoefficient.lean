module

public import ASDExplicitGamma.Cold.ScalarCoefficient

/-! # The genuine completed coefficient normalized by its true fixed frame -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- Positive spatial volume ensures a triadic open square is inhabited. -/
theorem cold_openCubeSet_nonempty (Q : TriadicCube 2) : (openCubeSet Q).Nonempty := by
  have hp : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet,volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  by_contra hn
  have he := Set.not_nonempty_iff_eq_empty.mp hn
  rw [he] at hp
  simp at hp

/-- The actual field sigmaBar_m^{-1} a_m; m is fixed across every lag and cell. -/
def coldNativeCoefficient (M : ABKModel 2) (m : ℤ) : Cutoff.CutoffSample 2 → RegCoeffField 2 :=
  fun ω => (Annealed.sigmaBar M m:ℝ)⁻¹ • Cutoff.coefficientCutoff M.nu m ω

/-- Exact positive lower ellipticity constant of the normalized actual field. -/
def coldNativeLower (M : ABKModel 2) (m : ℤ) : ℝ := (Annealed.sigmaBar M m:ℝ)⁻¹*M.nu

theorem coldNativeLower_pos (M : ABKModel 2) (m : ℤ) : 0 < coldNativeLower M m :=
  mul_pos (inv_pos.mpr (Annealed.sigmaBar_characterization M m).1) M.nu_pos

/-- The normalized field map is genuinely measurable on the original sample space. -/
theorem coldNativeCoefficient_measurable (M : ABKModel 2) (m : ℤ) :
    Measurable (coldNativeCoefficient M m) :=
  (measurable_scalar_coefficient (Annealed.sigmaBar M m:ℝ)⁻¹).comp
    (Cutoff.measurable_coefficientCutoff M.nu m)

/-- Every actual sample is pointwise uniformly elliptic on each cell. -/
theorem coldNativeCoefficient_elliptic (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    ∃ Λ : ℝ, IsEllipticFieldOn (coldNativeLower M m) Λ (cubeSet Q)
      (coldNativeCoefficient M m ω).toFun := by
  obtain ⟨Λ,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
  exact ⟨(Annealed.sigmaBar M m:ℝ)⁻¹*Λ,
    cold_isEllipticFieldOn_smul (inv_pos.mpr (Annealed.sigmaBar_characterization M m).1) hEll⟩

/-- The normalized genuine coefficient is locally a.e. uniformly elliptic at every sample. -/
theorem coldNativeCoefficient_locallyElliptic (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) : Ch04.AELocallyUniformlyEllipticField (coldNativeCoefficient M m ω) := by
  intro Q
  obtain ⟨Λ,hEll⟩ := coldNativeCoefficient_elliptic M m Q ω
  have hO := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  obtain ⟨x,hx⟩ := cold_openCubeSet_nonempty Q
  exact ⟨coldNativeLower M m,Λ,coldNativeLower_pos M m,(hO.2 x hx).2.1,
    IsAEEllipticFieldOn.of_isEllipticFieldOn hO⟩

/-- The full local-ellipticity support event is measurable through countably many exact slices. -/
theorem cold_measurableSet_locallyElliptic :
    MeasurableSet {a : RegCoeffField 2 | Ch04.AELocallyUniformlyEllipticField a} := by
  classical
  have he : {a : RegCoeffField 2 | Ch04.AELocallyUniformlyEllipticField a} =
      ⋂ Q : TriadicCube 2, ⋃ k : ℕ, {a : RegCoeffField 2 | AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k,hk⟩ := ha Q
      have hkpos : (0:ℝ) < ((k:ℝ)+1)⁻¹ := by positivity
      have hk1 : (1:ℝ) ≤ (k:ℝ)+1 := by have hk0 := Nat.cast_nonneg (α := ℝ) k; linarith
      have hle : ((k:ℝ)+1)⁻¹ ≤ (k:ℝ)+1 := ((inv_le_one₀ (by positivity)).mpr hk1).trans hk1
      exact ⟨((k:ℝ)+1)⁻¹,(k:ℝ)+1,hkpos,hle,
        hk.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)⟩
  rw [he]
  exact MeasurableSet.iInter (fun Q => MeasurableSet.iUnion (fun k => LocalSigmaR_le (cubeSet Q) _
    (Ch04.measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)))

end ASDExplicitGamma.Cold
