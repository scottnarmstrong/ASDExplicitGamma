module

public import ASDExplicitGamma.Cold.TriadicParity
public import ASDExplicitGamma.Cold.NativeLocalResponse

/-! # The genuine four-colour independent native cell arrays -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
namespace ASDExplicitGamma.Cold

/-- Actual local cell observables are independent within each of the four literal parity classes.
Cell populations are unrestricted; only their shared scale and distinctness are used. -/
theorem cold_native_four_color_independent {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m n : ℤ) (hmn : m ≤ n)
    (C : ι → TriadicCube 2) (hC : Function.Injective C) (hscale : ∀ i, (C i).scale = n)
    {X : ∀ i, CutoffSample 2 → E i}
    (hX : ∀ i, @Measurable (CutoffSample 2) (E i) (cutoffSampleLocalSigma M m (cubeSet (C i))) _ (X i)) :
    ∀ c : Fin 4, ProbabilityTheory.iIndepFun
      (fun i : {i // coldCubeColor (C i) = c} => X i.val) (cutoffSampleLaw M).toMeasure := by
  intro c
  apply cold_iIndepFun_cutoffLocal M h hM m (fun i : {i // coldCubeColor (C i) = c} => cubeSet (C i.val))
    (fun i => measurableSet_cubeSet (C i.val))
  · intro i j hij x hx y hy
    have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hneq : C i.val ≠ C j.val := fun he => hval (hC he)
    have hsc : (C i.val).scale = (C j.val).scale := (hscale _).trans (hscale _).symm
    obtain ⟨k,hk⟩ := cold_same_color_separation hsc hneq (i.property.trans j.property.symm) hx hy
    refine ⟨k,?_⟩
    have hp : (3:ℝ)^m ≤ (3:ℝ)^(C i.val).scale :=
      zpow_le_zpow_right₀ (by norm_num) (by rw [hscale]; exact hmn)
    exact hp.trans hk
  · intro i
    exact hX i.val

/-- The literal trace array is a native four-colour family; independence is now a theorem. -/
theorem cold_native_trace_four_color {ι : Type*} (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m n : ℤ) (hmn : m ≤ n) (C : ι → TriadicCube 2) (hC : Function.Injective C)
    (hscale : ∀ i, (C i).scale = n) : ∀ c : Fin 4, ProbabilityTheory.iIndepFun
      (fun i : {i // coldCubeColor (C i) = c} => coldNativeCellTrace M m (C i.val))
      (cutoffSampleLaw M).toMeasure :=
  cold_native_four_color_independent M h hM m n hmn C hC hscale (fun i => coldNativeCellTrace_local M m (C i))

end ASDExplicitGamma.Cold
