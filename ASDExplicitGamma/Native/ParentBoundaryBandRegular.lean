module

public import ASDExplicitGamma.Native.ParentBoundaryBandSymmetry
public import ASDExplicitGamma.Inverse.BankResponseMeasurable
public import ASDExplicitGamma.Cold.ScalarCoefficient
public import ASDExplicitGamma.Variational.EnergyMap
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine

/-! Genuine regularity and local ellipticity of arbitrary finite weighted bands. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
noncomputable section

def parentBoundaryBandRegCoefficient (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : RegCoeffField 2 :=
  Cutoff.coefficientCutoff M.nu m ω+
    ∑ k ∈ Finset.Ioc m J, weights k • ShellField.forgetShell (ω.1 k)

theorem parent_boundary_band_reg_measurable (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) :
    Measurable (parentBoundaryBandRegCoefficient M m J weights) := by
  unfold parentBoundaryBandRegCoefficient
  apply (Cutoff.measurable_coefficientCutoff M.nu m).add
  apply Finset.measurable_sum
  intro k hk
  exact (ASDExplicitGamma.Cold.measurable_scalar_coefficient (weights k)).comp
    (ShellField.measurable_forgetShell.comp
      ((measurable_pi_apply k).comp measurable_subtype_coe))

theorem parent_boundary_band_reg_apply (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) :
    (parentBoundaryBandRegCoefficient M m J weights ω).toFun x =
      attenuatedCoefficient M m J weights ω x := by
  simp [parentBoundaryBandRegCoefficient, attenuatedCoefficient,
    RegCoeffField.finset_sum_apply]

private theorem parent_boundary_band_symmPart_add (A B : Mat 2) :
    Homogenization.symmPart (A+B)=Homogenization.symmPart A+Homogenization.symmPart B := by
  ext i j
  simp only [Homogenization.symmPart,Matrix.add_apply]
  ring

private theorem parent_boundary_band_attenuated_symmPart (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (attenuatedCoefficient M m J weights ω x)=
      M.nu • (1:Mat 2) := by
  unfold attenuatedCoefficient
  rw [parent_boundary_band_symmPart_add,Cutoff.symmPart_coefficientCutoff]
  have hsum : Homogenization.symmPart
      (∑ k ∈ Finset.Ioc m J, weights k • ShellField.forgetShell (ω.1 k) x)=0 := by
    ext i j
    simp only [Homogenization.symmPart,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
      ShellField.forgetShell_apply]
    rw [← Finset.sum_add_distrib]
    apply (div_eq_zero_iff).mpr
    left
    apply Finset.sum_eq_zero
    intro k hk
    rw [(ω.1 k).skew_entry x i j]
    ring
  rw [hsum]
  simp

private theorem parent_boundary_band_attenuated_entry_bound (M : ABKModel 2) (ell : ℕ)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (hcover : ∀ x ∈ cubeSet Q, x ∈ openCubeSet (originCube 2 (ell:ℤ)))
    {x : Vec 2} (hx : x ∈ cubeSet Q) (i j : Fin 2) :
    |attenuatedCoefficient M m J weights ω x i j| ≤
      M.nu+Cutoff.cutoffLocalControl (ell:ℤ) m ω+
        ∑ k ∈ Finset.Ioc m J,
          |weights k| * localCubeControl (ell:ℤ) (ω.1 k) := by
  classical
  have hxN := hcover x hx
  have hbase := Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le
    (ell:ℤ) m ω hxN i j
  have hsum : |∑ k ∈ Finset.Ioc m J, weights k*ω.1 k x i j| ≤
      ∑ k ∈ Finset.Ioc m J, |weights k| * localCubeControl (ell:ℤ) (ω.1 k) := by
    calc
      |∑ k ∈ Finset.Ioc m J, weights k*ω.1 k x i j| ≤
          ∑ k ∈ Finset.Ioc m J, |weights k*ω.1 k x i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_entry_le_localCubeControl (ell:ℤ) (ω.1 k) hxN i j) (abs_nonneg _)
  have hsumEntry :
      (∑ k ∈ Finset.Ioc m J, weights k • (ω.1 k).forgetShell x) i j =
        ∑ k ∈ Finset.Ioc m J, weights k*ω.1 k x i j := by
    simp [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,ShellField.forgetShell_apply]
  rw [attenuatedCoefficient,Matrix.add_apply,hsumEntry]
  calc
    |Cutoff.coefficientCutoff M.nu m ω x i j+
        ∑ k ∈ Finset.Ioc m J, weights k*ω.1 k x i j| ≤
      |Cutoff.coefficientCutoff M.nu m ω x i j|+
        |∑ k ∈ Finset.Ioc m J, weights k*ω.1 k x i j| := abs_add_le _ _
    _ ≤ M.nu+Cutoff.cutoffLocalControl (ell:ℤ) m ω+
        ∑ k ∈ Finset.Ioc m J, |weights k| * localCubeControl (ell:ℤ) (ω.1 k) :=
      add_le_add hbase hsum

theorem parent_boundary_band_elliptic_cube (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2) :
    ∃ Lam : ℝ,M.nu≤Lam ∧ IsEllipticFieldOn M.nu Lam (cubeSet Q)
      (attenuatedCoefficient M m J weights ω) := by
  classical
  let K : Set (Vec 2) := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨ell,hcover⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact hK
  let C : ℝ := M.nu+Cutoff.cutoffLocalControl (ell:ℤ) m ω+
    ∑ k ∈ Finset.Ioc m J, |weights k| * localCubeControl (ell:ℤ) (ω.1 k)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg M.nu_pos.le (Cutoff.cutoffLocalControl_nonneg (ell:ℤ) m ω))
      (Finset.sum_nonneg fun k hk => mul_nonneg (abs_nonneg _) (localCubeControl_nonneg _ _))
  have hcover' : ∀ x ∈ cubeSet Q, x ∈ openCubeSet (originCube 2 (ell:ℤ)) :=
    fun x hx => hcover (subset_closure hx)
  have hcubeEll : IsEllipticFieldOn M.nu
      (((2:ℝ)*2*C^2+M.nu^2)/M.nu) (cubeSet Q)
      (parentBoundaryBandRegCoefficient M m J weights ω).toFun := by
    refine ⟨?_,?_⟩
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      exact ((parentBoundaryBandRegCoefficient M m J weights ω).entry_measurable i j).ite
        (measurableSet_cubeSet Q) measurable_const
    · intro x hx
      apply Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
        (show Homogenization.symmPart
          ((parentBoundaryBandRegCoefficient M m J weights ω).toFun x)=
            M.nu • (1:Mat 2) by
          rw [parent_boundary_band_reg_apply]
          exact parent_boundary_band_attenuated_symmPart M m J weights ω x)
      intro i j
      rw [parent_boundary_band_reg_apply]
      simpa [C] using parent_boundary_band_attenuated_entry_bound M ell m J weights ω Q hcover' hx i j
  refine ⟨((2:ℝ)*2*C^2+M.nu^2)/M.nu,?_,?_⟩
  · exact (le_div_iff₀ M.nu_pos).2 (by nlinarith [sq_nonneg C])
  · have heq : (parentBoundaryBandRegCoefficient M m J weights ω).toFun=
        attenuatedCoefficient M m J weights ω := by
      funext x
      exact parent_boundary_band_reg_apply M m J weights ω x
    rwa [heq] at hcubeEll

/-- The actual finite weighted law has the exact local ellipticity carrier. -/
theorem parent_boundary_band_locally_elliptic (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (omega : Cutoff.CutoffSample 2) :
    Book.Ch04.AELocallyUniformlyEllipticField (parentBoundaryBandRegCoefficient M m J weights omega) := by
  intro Q
  obtain ⟨Lam,hLam,hEll⟩ := parent_boundary_band_elliptic_cube M m J weights omega Q
  refine ⟨M.nu,Lam,M.nu_pos,hLam,?_⟩
  have he := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  change IsAEEllipticFieldOn M.nu Lam (openCubeSet Q)
    (parentBoundaryBandRegCoefficient M m J weights omega).toFun
  have heq : (parentBoundaryBandRegCoefficient M m J weights omega).toFun=
      attenuatedCoefficient M m J weights omega := by
    funext x
    exact parent_boundary_band_reg_apply M m J weights omega x
  rw [heq]
  exact IsAEEllipticFieldOn.of_isEllipticFieldOn he

/-- The actual finite weighted coefficient has a genuine variational
coarse matrix on every square, without a coarse-matrix witness premise. -/
theorem parent_boundary_band_coarse_exists (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (omega : Cutoff.CutoffSample 2) (Q : TriadicCube 2) :
    ∃ Abar : BlockMat 2,IsCoarseBlockMatrix (openCubeSet Q)
      (attenuatedCoefficient M m J weights omega) Abar := by
  obtain ⟨Lam,_hLam,hEll⟩ := parent_boundary_band_elliptic_cube M m J weights omega Q
  have he := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  obtain ⟨_,hcoarse,_,_,_,_,_,_⟩ := exists_energyMap_coarseData
    (isOpenBoundedConvexDomain_openCubeSet Q) he (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
  exact ⟨_,hcoarse⟩

end
end ASDExplicitGamma.Native
