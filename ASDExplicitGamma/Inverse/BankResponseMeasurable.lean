module

public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Variational.TraceDefect
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine
public import ASDExplicitGamma.Cold.ScalarCoefficient

/-! Measurability infrastructure for the literal finite attenuated root response. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

private noncomputable def bankAttenuatedRegCoefficient (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : RegCoeffField 2 :=
  Cutoff.coefficientCutoff M.nu m ω +
    ∑ k ∈ Finset.Ioc m J, weights k • ShellField.forgetShell (ω.1 k)

private theorem bankAttenuatedRegCoefficient_measurable (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) :
    Measurable (bankAttenuatedRegCoefficient M m J weights) := by
  unfold bankAttenuatedRegCoefficient
  apply (Cutoff.measurable_coefficientCutoff M.nu m).add
  apply Finset.measurable_sum
  intro k hk
  exact (ASDExplicitGamma.Cold.measurable_scalar_coefficient (weights k)).comp
    (ShellField.measurable_forgetShell.comp
      ((measurable_pi_apply k).comp measurable_subtype_coe))

private theorem bankAttenuatedRegCoefficient_apply (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) :
    (bankAttenuatedRegCoefficient M m J weights ω).toFun x =
      attenuatedCoefficient M m J weights ω x := by
  simp [bankAttenuatedRegCoefficient, attenuatedCoefficient,
    RegCoeffField.finset_sum_apply]

private theorem bank_symmPart_add (A B : Mat 2) :
    Homogenization.symmPart (A + B) =
      Homogenization.symmPart A + Homogenization.symmPart B := by
  ext i j
  simp only [Homogenization.symmPart, Matrix.add_apply]
  ring

private theorem bank_attenuated_symmPart (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (attenuatedCoefficient M m J weights ω x) =
      M.nu • (1 : Mat 2) := by
  unfold attenuatedCoefficient
  rw [bank_symmPart_add, Cutoff.symmPart_coefficientCutoff]
  have hsum : Homogenization.symmPart
      (∑ k ∈ Finset.Ioc m J,
        weights k • ShellField.forgetShell (ω.1 k) x) = 0 := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, ShellField.forgetShell_apply]
    rw [← Finset.sum_add_distrib]
    apply (div_eq_zero_iff).mpr
    left
    apply Finset.sum_eq_zero
    intro k hk
    rw [(ω.1 k).skew_entry x i j]
    ring
  rw [hsum]
  simp

private theorem bank_attenuated_entry_bound (M : ABKModel 2) (ell : ℕ)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (hcover : ∀ x ∈ cubeSet Q, x ∈ openCubeSet (originCube 2 (ell : ℤ)))
    {x : Vec 2} (hx : x ∈ cubeSet Q) (i j : Fin 2) :
    |attenuatedCoefficient M m J weights ω x i j| ≤
      M.nu + Cutoff.cutoffLocalControl (ell : ℤ) m ω +
        ∑ k ∈ Finset.Ioc m J,
          |weights k| * localCubeControl (ell : ℤ) (ω.1 k) := by
  classical
  have hxN := hcover x hx
  have hbase := Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le
    (ell : ℤ) m ω hxN i j
  have hsum : |∑ k ∈ Finset.Ioc m J,
        weights k * ω.1 k x i j| ≤
      ∑ k ∈ Finset.Ioc m J,
        |weights k| * localCubeControl (ell : ℤ) (ω.1 k) := by
    calc
      |∑ k ∈ Finset.Ioc m J, weights k * ω.1 k x i j| ≤
          ∑ k ∈ Finset.Ioc m J, |weights k * ω.1 k x i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ioc m J,
          |weights k| * localCubeControl (ell : ℤ) (ω.1 k) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_entry_le_localCubeControl (ell : ℤ) (ω.1 k) hxN i j)
          (abs_nonneg _)
  have hsumEntry :
      (∑ k ∈ Finset.Ioc m J, weights k • (ω.1 k).forgetShell x) i j =
        ∑ k ∈ Finset.Ioc m J, weights k * ω.1 k x i j := by
    simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      ShellField.forgetShell_apply]
  rw [attenuatedCoefficient, Matrix.add_apply, hsumEntry]
  calc
    |Cutoff.coefficientCutoff M.nu m ω x i j +
        ∑ k ∈ Finset.Ioc m J, weights k * ω.1 k x i j| ≤
      |Cutoff.coefficientCutoff M.nu m ω x i j| +
        |∑ k ∈ Finset.Ioc m J, weights k * ω.1 k x i j| := abs_add_le _ _
    _ ≤ M.nu + Cutoff.cutoffLocalControl (ell : ℤ) m ω +
        ∑ k ∈ Finset.Ioc m J, |weights k| * localCubeControl (ell : ℤ) (ω.1 k) :=
      add_le_add hbase hsum
    _ = _ := rfl

private theorem bankAttenuatedRegCoefficient_locallyElliptic (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    Book.Ch04.AELocallyUniformlyEllipticField
      (bankAttenuatedRegCoefficient M m J weights ω) := by
  intro Q
  classical
  let K : Set (Vec 2) := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨N, hcover⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact hK
  let C : ℝ := M.nu + Cutoff.cutoffLocalControl (N : ℤ) m ω +
    ∑ k ∈ Finset.Ioc m J, |weights k| * localCubeControl (N : ℤ) (ω.1 k)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg M.nu_pos.le
      (Cutoff.cutoffLocalControl_nonneg (N : ℤ) m ω))
      (Finset.sum_nonneg fun k hk => mul_nonneg (abs_nonneg _)
        (localCubeControl_nonneg (N : ℤ) (ω.1 k)))
  have hcover' : ∀ x ∈ cubeSet Q,
      x ∈ openCubeSet (originCube 2 (N : ℤ)) := fun x hx => hcover (subset_closure hx)
  have hcubeEll : IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * C ^ 2 + M.nu ^ 2) / M.nu)
      (cubeSet Q) (bankAttenuatedRegCoefficient M m J weights ω).toFun := by
    refine ⟨?_, ?_⟩
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      exact ((bankAttenuatedRegCoefficient M m J weights ω).entry_measurable i j).ite
        (measurableSet_cubeSet Q) measurable_const
    · intro x hx
      apply Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
        (show Homogenization.symmPart
          ((bankAttenuatedRegCoefficient M m J weights ω).toFun x) =
            M.nu • (1 : Mat 2) from by
              rw [bankAttenuatedRegCoefficient_apply]
              exact bank_attenuated_symmPart M m J weights ω x)
      intro i j
      rw [bankAttenuatedRegCoefficient_apply]
      simpa [C] using bank_attenuated_entry_bound M N m J weights ω Q hcover' hx i j
  have hopen := hcubeEll.mono (measurableSet_openCubeSet Q)
    (openCubeSet_subset_cubeSet Q)
  refine ⟨M.nu, ((2 : ℝ) * 2 * C ^ 2 + M.nu ^ 2) / M.nu,
    M.nu_pos, ?_, IsAEEllipticFieldOn.of_isEllipticFieldOn hopen⟩
  exact (le_div_iff₀ M.nu_pos).2 (by nlinarith [sq_nonneg C])

theorem root_inverse_response_measurable (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (Q : TriadicCube 2) :
    Measurable (rootInverseResponse M Q m J weights) := by
  let X := bankAttenuatedRegCoefficient M m J weights
  have hX : Measurable X := bankAttenuatedRegCoefficient_measurable M m J weights
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    fun ω => bankAttenuatedRegCoefficient_locallyElliptic M m J weights ω
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet
    hX hEll Q
  let L : Mat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
    { toFun := fun A => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) A B
      map_smul' := fun c A => map_smul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) c A }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hnorm : Measurable (fun ω =>
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)‖) := by
    exact hL.norm.measurable.comp hLR
  have hfield (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M m J weights ω = (X ω).toFun := by
    funext x
    exact (bankAttenuatedRegCoefficient_apply M m J weights ω x).symm
  change Measurable (fun ω =>
    (Annealed.sigmaBar M m : ℝ) *
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        ((coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)).lowerRight)‖)
  have hEq : (fun ω => (Annealed.sigmaBar M m : ℝ) *
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        ((coarseBlockMatrix (cubeSet Q)
          (attenuatedCoefficient M m J weights ω)).lowerRight)‖) =
    (fun ω => (Annealed.sigmaBar M m : ℝ) *
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)‖) := by
    funext ω
    rw [hfield ω]
  rw [hEq]
  exact hnorm.const_mul _

end ASDExplicitGamma.Inverse
