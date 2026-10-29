module

public import ASDExplicitGamma.Inverse.AssemblyTraceRoot
public import ASDExplicitGamma.Inverse.BankResponseMeasurable
public import ASDExplicitGamma.Triadic.SensitivityDerivative
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine
public import ASDExplicitGamma.Cold.ScalarCoefficient

/-! Measurability and positivity of the actual framed trace. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Variational
open ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

private def traceAttenuatedRegCoefficient (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : RegCoeffField 2 :=
  Cutoff.coefficientCutoff M.nu m ω+
    ∑ k ∈ Finset.Ioc m J, weights k • ShellField.forgetShell (ω.1 k)

private theorem trace_attenuated_reg_coefficient_measurable (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) :
    Measurable (traceAttenuatedRegCoefficient M m J weights) := by
  unfold traceAttenuatedRegCoefficient
  apply (Cutoff.measurable_coefficientCutoff M.nu m).add
  apply Finset.measurable_sum
  intro k hk
  exact (ASDExplicitGamma.Cold.measurable_scalar_coefficient (weights k)).comp
    (ShellField.measurable_forgetShell.comp
      ((measurable_pi_apply k).comp measurable_subtype_coe))

private theorem trace_attenuated_reg_coefficient_apply (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) :
    (traceAttenuatedRegCoefficient M m J weights ω).toFun x =
      attenuatedCoefficient M m J weights ω x := by
  simp [traceAttenuatedRegCoefficient, attenuatedCoefficient,
    RegCoeffField.finset_sum_apply]

private theorem trace_symmPart_add (A B : Mat 2) :
    Homogenization.symmPart (A+B)=Homogenization.symmPart A+Homogenization.symmPart B := by
  ext i j
  simp only [Homogenization.symmPart,Matrix.add_apply]
  ring

private theorem trace_attenuated_symmPart (M : ABKModel 2) (m J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (attenuatedCoefficient M m J weights ω x)=
      M.nu • (1:Mat 2) := by
  unfold attenuatedCoefficient
  rw [trace_symmPart_add,Cutoff.symmPart_coefficientCutoff]
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

private theorem trace_attenuated_entry_bound (M : ABKModel 2) (ell : ℕ)
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

private theorem trace_attenuated_locally_elliptic (M : ABKModel 2)
    (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    Book.Ch04.AELocallyUniformlyEllipticField
      (traceAttenuatedRegCoefficient M m J weights ω) := by
  intro Q
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
      (traceAttenuatedRegCoefficient M m J weights ω).toFun := by
    refine ⟨?_,?_⟩
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      exact ((traceAttenuatedRegCoefficient M m J weights ω).entry_measurable i j).ite
        (measurableSet_cubeSet Q) measurable_const
    · intro x hx
      apply Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
        (show Homogenization.symmPart
          ((traceAttenuatedRegCoefficient M m J weights ω).toFun x)=
            M.nu • (1:Mat 2) by
          rw [trace_attenuated_reg_coefficient_apply]
          exact trace_attenuated_symmPart M m J weights ω x)
      intro i j
      rw [trace_attenuated_reg_coefficient_apply]
      simpa [C] using trace_attenuated_entry_bound M ell m J weights ω Q hcover' hx i j
  have hopen := hcubeEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  refine ⟨M.nu,((2:ℝ)*2*C^2+M.nu^2)/M.nu,M.nu_pos,?_,
    IsAEEllipticFieldOn.of_isEllipticFieldOn hopen⟩
  exact (le_div_iff₀ M.nu_pos).2 (by nlinarith [sq_nonneg C])

/-- The actual four-load trace is measurable in the full cutoff law. -/
theorem root_trace_observable_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (m N K₀ : ℤ) (weights : ℤ → ℝ) :
    Measurable (rootTraceObservable M Q m N K₀ weights) := by
  let X := traceAttenuatedRegCoefficient M m N weights
  have hX : Measurable X := trace_attenuated_reg_coefficient_measurable M m N weights
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    fun ω => trace_attenuated_locally_elliptic M m N weights ω
  have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet
    hX hEll Q
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet
    hX hEll Q
  have hTraceUL : Measurable (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q)
      (X ω).toFun).upperLeft)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i)
  have hTraceLR : Measurable (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q)
      (X ω).toFun).lowerRight)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
    exact Finset.measurable_sum _ (fun i _ =>
      (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i)
  have hfield (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
      (X ω).toFun x=attenuatedCoefficient M m N weights ω x :=
    trace_attenuated_reg_coefficient_apply M m N weights ω x
  change Measurable (fun ω => rootTraceObservable M Q m N K₀ weights ω)
  rw [show (fun ω => rootTraceObservable M Q m N K₀ weights ω) =
      (fun ω => traceDefect (cubeSet Q) (attenuatedCoefficient M m N weights ω)
        (Annealed.sigmaBar M K₀:ℝ)+4) by
    funext ω
    exact root_trace_observable_eq_trace_defect M Q m N K₀ weights ω]
  have hUL' : (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m N weights ω)).upperLeft)) =
      (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)) := by
    funext ω
    congr 3
    funext x
    exact (hfield ω x).symm
  have hLR' : (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m N weights ω)).lowerRight)) =
      (fun ω => Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
    funext ω
    congr 3
    funext x
    exact (hfield ω x).symm
  unfold traceDefect
  have hrewrite :
      (fun ω => ((Annealed.sigmaBar M K₀:ℝ)⁻¹ *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q)
            (attenuatedCoefficient M m N weights ω)).upperLeft)+
        (Annealed.sigmaBar M K₀:ℝ) *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q)
            (attenuatedCoefficient M m N weights ω)).lowerRight)-4)+4) =
      (fun ω => ((Annealed.sigmaBar M K₀:ℝ)⁻¹ *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)+
        (Annealed.sigmaBar M K₀:ℝ) *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)-4)+4) := by
    funext ω
    rw [congrFun hUL' ω,congrFun hLR' ω]
  rw [hrewrite]
  have hcancel :
      (fun ω => ((Annealed.sigmaBar M K₀:ℝ)⁻¹ *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)+
        (Annealed.sigmaBar M K₀:ℝ) *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)-4)+4) =
      (fun ω => (Annealed.sigmaBar M K₀:ℝ)⁻¹ *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)+
        (Annealed.sigmaBar M K₀:ℝ) *
          Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
    funext ω
    ring
  rw [hcancel]
  exact (hTraceUL.const_mul _).add (hTraceLR.const_mul _)

/-- The actual full trace is nonnegative by positivity of the four framed
response loadings. -/
theorem root_trace_observable_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (m N K₀ : ℤ) (hm : m ≤ N) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ rootTraceObservable M Q m N K₀ weights ω := by
  let A := coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m N weights ω)
  let σ := (Annealed.sigmaBar M K₀:ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M K₀).1
  have hbook : Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q M.nu M.nu_pos
        (oldResponseCoefficient Q m ω+
          laterResponseCoefficient Q m N (sourceBandWeights m weights) ω)) = A :=
    attenuated_sensitivity_matrix_eq M Q m m N le_rfl hm weights ω
  have hquad (P : BlockVec 2) : 0 ≤ blockVecDot P (blockMatVecMul A P) := by
    by_cases hP : P=0
    · rw [hP]
      simp [blockVecDot,blockMatVecMul,vecDot,matVecMul]
    · rw [← hbook]
      exact (Book.Ch02.blockCoarseMatrixTheory (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q M.nu M.nu_pos
          (oldResponseCoefficient Q m ω+
            laterResponseCoefficient Q m N (sourceBandWeights m weights) ω))).block_matrix_posDef
              P hP |>.le
  have htr := full_response_frame_trace_eq_scaled_loads σ A hσ
  have hterms : 0 ≤ ∑ j : Fin 2 × Bool,
      let P := fullResponseTraceLoad j
      let Pσ := ((Real.sqrt σ)⁻¹ • P.1,Real.sqrt σ • P.2)
      blockVecDot Pσ (blockMatVecMul A Pσ) :=
    Finset.sum_nonneg fun j _ => by
      dsimp
      exact hquad _
  have heq : rootTraceObservable M Q m N K₀ weights ω =
      ∑ j : Fin 2 × Bool,
        let P := fullResponseTraceLoad j
        let Pσ := ((Real.sqrt σ)⁻¹ • P.1,Real.sqrt σ • P.2)
        blockVecDot Pσ (blockMatVecMul A Pσ) := by
    simpa only [rootTraceObservable,A,σ] using htr
  rw [heq]
  exact hterms

end
end ASDExplicitGamma.Inverse
