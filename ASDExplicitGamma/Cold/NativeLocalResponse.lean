module

public import ASDExplicitGamma.Cold.NativeLocalTrace
public import ASDExplicitGamma.Cold.NativeFrameTrace

/-! # Local measurability of the actual full response in the true fixed frame -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.BadEvents
namespace ASDExplicitGamma.Cold

/-- The actual doubled coarse response in the true frame, evaluated on the original cutoff carrier. -/
def coldNativeResponse (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) : CutoffSample 2 → FullBlockMat 2 :=
  fun ω => toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M m:ℝ)
    (coarseBlockMatrix (cubeSet Q) (coefficientCutoff M.nu m ω).toFun))

/-- Measurability of all quadratic Mu observables gives measurability of the literal full framed matrix. -/
theorem cold_fullResponse_measurable {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    (σ : ℝ) (a : Ω → CoeffField 2) (hMu : ∀ P, Measurable (fun ω => Mu (cubeSet Q) P (a ω))) :
    Measurable (fun ω => toFullBlockMat (Variational.frameMatrix σ (coarseBlockMatrix (cubeSet Q) (a ω)))) := by
  apply measurable_pi_iff.mpr
  intro α
  apply measurable_pi_iff.mpr
  intro β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      change Measurable (fun ω => σ⁻¹*(coarseBlockMatrix (cubeSet Q) (a ω)).upperLeft i j)
      apply Measurable.const_mul
      simp_rw [coarseBlockMatrix_upperLeft_apply]
      split_ifs
      · exact (hMu _).const_mul 2
      · exact ((hMu _).sub (hMu _)).sub (hMu _)
    | inr j =>
      change Measurable (fun ω => (coarseBlockMatrix (cubeSet Q) (a ω)).upperRight i j)
      simp_rw [coarseBlockMatrix_upperRight_apply]
      exact ((hMu _).sub (hMu _)).sub (hMu _)
  | inr i =>
    cases β with
    | inl j =>
      change Measurable (fun ω => (coarseBlockMatrix (cubeSet Q) (a ω)).lowerLeft i j)
      simp_rw [coarseBlockMatrix_lowerLeft_apply]
      exact ((hMu _).sub (hMu _)).sub (hMu _)
    | inr j =>
      change Measurable (fun ω => σ*(coarseBlockMatrix (cubeSet Q) (a ω)).lowerRight i j)
      apply Measurable.const_mul
      simp_rw [coarseBlockMatrix_lowerRight_apply]
      split_ifs
      · exact (hMu _).const_mul 2
      · exact ((hMu _).sub (hMu _)).sub (hMu _)

/-- The full actual framed response reads only the completed integral-local field on its cell. -/
theorem coldNativeResponse_local (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    @Measurable (CutoffSample 2) (FullBlockMat 2) (cutoffSampleLocalSigma M m (cubeSet Q)) _
      (coldNativeResponse M m Q) := by
  let instColdResponseLocal : MeasurableSpace (CutoffSample 2) := cutoffSampleLocalSigma M m (cubeSet Q)
  exact cold_fullResponse_measurable Q _ _
    (fun P => measurable_Mu_coefficientCutoff_cutoffSampleLocal M m Q Set.Subset.rfl P)

/-- The full actual framed response is also genuinely measurable on the original sample carrier. -/
theorem coldNativeResponse_measurable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    Measurable (coldNativeResponse M m Q) :=
  cold_fullResponse_measurable Q _ _ (fun P => measurable_comp_Mu_cubeSet
    (measurable_coefficientCutoff M.nu m) (coefficientCutoff_aeLocallyUniformlyEllipticField M m) Q P)

/-- The framed native matrix is exactly the coarse matrix of the actual normalized coefficient. -/
theorem coldNativeResponse_eq_normalized (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    coldNativeResponse M m Q ω = toFullBlockMat (coarseBlockMatrix (openCubeSet Q) (coldNativeCoefficient M m ω).toFun) := by
  obtain ⟨Λ,hEll⟩ := Variational.cutoff_isEllipticFieldOn_cube M m ω Q
  unfold coldNativeResponse
  rw [← cold_coarse_cube_open]
  exact (congrArg toFullBlockMat (cold_coarse_frame M.nu_pos hEll (Annealed.sigmaBar_characterization M m).1)).symm

end ASDExplicitGamma.Cold
