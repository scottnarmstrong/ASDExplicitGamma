module

public import ASDExplicitGamma.Scalar.DropCombineBridge
public import ASDExplicitGamma.Scalar.DropOneShellGen
public import ASDExplicitGamma.Scalar.LowerCorridorGen
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Scalar.ColdReciprocalNormalization
public import ASDExplicitGamma.Scalar.MolecularStartupScale
public import ASDExplicitGamma.Scalar.ReciprocalMolecular
public import ASDExplicitGamma.Scalar.ReciprocalTrueFrame
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Cold.NativeThetaScaling
public import ASDExplicitGamma.Numerics.Cold.Basic
public import ASDExplicitGamma.Joint.GateStep

/-! JO-LOWER-SCALAR-N: the lower scalar conclusion at `N` from the reciprocal drop at every
earlier label.  The flat leg is discharged by `flat_expectation_package`; the certified
sharp constant enters only through the bundle `DropRCert`. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar

noncomputable section

theorem drop_unit_vector : ∃ e : Vec 2, vecDot e e = 1 ∧ Book.Ch02.vecNorm e = 1 ∧
    vecNormSq e = 1 := by
  refine ⟨fun j => if j = 0 then 1 else 0, ?_, ?_, ?_⟩
  · simp [vecDot, Fin.sum_univ_two]
  · simp only [Book.Ch02.vecNorm]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two]
  · simp [vecNormSq, vecDot, Fin.sum_univ_two]

/-- Rectangle containing the open cube `originCube 2 n`. -/
theorem drop_exists_rect (n : ℤ) : ∃ (a b c d : ℝ) (hab : a < b) (hcd : c < d),
    openCubeSet (originCube 2 n) ⊆ openRectangle a b c d := by
  obtain ⟨R, hR⟩ := (isBounded_cubeSet (originCube 2 n)).exists_norm_le
  refine ⟨-(|R| + 1), |R| + 1, -(|R| + 1), |R| + 1, by linarith [abs_nonneg R],
    by linarith [abs_nonneg R], ?_⟩
  intro x hx
  have hn : ‖x‖ ≤ R := hR x (openCubeSet_subset_cubeSet _ hx)
  have h0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x 0
  have h1 : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x 1
  have := le_abs_self R
  refine ⟨?_, ?_⟩ <;> constructor <;> [skip; skip; skip; skip] <;>
    first
    | (have := neg_abs_le (x 0); linarith)
    | (have := le_abs_self (x 0); linarith)
    | (have := neg_abs_le (x 1); linarith)
    | (have := le_abs_self (x 1); linarith)

/-- Generic: `C♯(Fflat, Fdef)` is below the explicit sharp formula in the defect cap. -/
theorem drop_Csharp_le_gen (Fflat Fdef Ddef : ℝ) (hF0 : 0 ≤ Fflat)
    (hcap : Fflat ≤ (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)))
    (hdef0 : 0 ≤ Fdef) (hdef : Fdef ≤ Ddef) :
    newResolventCSharp Fflat Fdef ≤
      (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) +
        (141 / 50 : ℝ) * Real.sqrt ((1557 / 1000 : ℝ) *
          ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) * Ddef) +
        (44 / 25 : ℝ) * Ddef := by
  unfold newResolventCSharp
  have hs : Real.sqrt (Fflat * Fdef) ≤ Real.sqrt
      ((1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) * Ddef) :=
    Real.sqrt_le_sqrt (mul_le_mul hcap hdef hdef0 (hF0.trans hcap))
  nlinarith

/-- The facts about the R-certified defect/sharp/charge/gain constants consumed by the drop.
`Ddef` is the certified defect value (to be `evalReal scalarRealEnv quarticDefectRExpr`), `Csh` the
sharp constant, `Chg` the one-shell charge, `G` the reciprocal gain. -/
structure DropRCert (M : ABKModel 2) (h : ℝ) (N : ℤ) where
  Ddef : ℝ
  Csh : ℝ
  Chg : ℝ
  G : ℝ
  hDdef0 : 0 ≤ Ddef
  hdef : ∀ i : ℤ, i < N → dropFdef M h i ≤ Ddef
  hCsh : Csh = (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) +
        (141 / 50 : ℝ) * Real.sqrt ((1557 / 1000 : ℝ) *
          ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)) * Ddef) +
        (44 / 25 : ℝ) * Ddef
  hChg : Chg = Csh * (((11 / 5 : ℝ) * (17 / 50000)) / (1 - (11 / 5 : ℝ) * (17 / 50000)))
  hG : G = evalReal scalarRealEnv lowerBaseExpr - Chg / (31 / 50)
  hGm : (12493 / 40000 : ℝ) ≤ G

theorem DropRCert.csh_nonneg {M : ABKModel 2} {h : ℝ} {N : ℤ} (c : DropRCert M h N) :
    0 ≤ c.Csh := by
  rw [c.hCsh]
  have := c.hDdef0
  positivity

/-- JO-LOWER-SCALAR-N from the R-certificate bundle. -/
theorem jo_lower_scalar_N_of_R_cert (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ) (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n)
    (cert : DropRCert M h N) : LowerScalarConclusion M h N := by
  obtain ⟨e, he, he1, he2⟩ := drop_unit_vector
  refine lower_corridor_of_one_shell_decrements_gen cert.G cert.hGm M h hM hγ N e he
    hprev ?_
  intro i hi
  obtain ⟨a, b, c, d, hab, hcd, hQ⟩ := drop_exists_rect (i + 129)
  have hpi : ∀ n : ℤ, n ≤ i → nativeInductionState M h n :=
    fun n hn => hprev n (lt_of_le_of_lt hn hi)
  have hF := flat_expectation_package M h i hab hcd hQ e hM hγ
    (fun n hn => hprev n (lt_of_lt_of_le hn hi.le)) he1
  have hq := drop_quartic_bound_of_combine M h i hab hcd hQ e hM hγ hpi he1 he2
    (Fflat := (1557 / 1000 : ℝ) * ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ)))
    hF le_rfl
  have hCq := drop_Csharp_le_gen _ (dropFdef M h i) cert.Ddef hF.1 le_rfl
    (defectFdefR_nonneg _ _ _) (cert.hdef i hi)
  rw [← cert.hCsh] at hCq
  exact drop_one_shell_gen cert.Csh cert.Chg cert.G cert.csh_nonneg cert.hChg cert.hG
    M h hM hγ N hprev i hi e he _ hCq hq

end

end ASDExplicitGamma.Joint
