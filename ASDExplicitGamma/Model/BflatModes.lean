module

public import ASDExplicitGamma.Cold.SquareSineTest
public import ASDExplicitGamma.Triadic.NeumannModes
public import Homogenization.Sobolev.PotentialSolenoidalL2
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization
public import Homogenization.PDE.DirichletRHS

/-! # Actual zero-trace sine modes for the B-flat square projection -/

@[expose] public section

open Homogenization
open ASDExplicitGamma.Triadic
open MeasureTheory

namespace ASDExplicitGamma.Model

/-- The centered triadic cube whose open carrier is the unit square. -/
def bflatUnitSquare : TriadicCube 2 := ⟨0, fun _ => 0⟩

/-- The source positive sine frequencies, indexed from zero for Lean sums. -/
def bflatSquareModeIndex (m n : ℕ) : Fin 2 → ℕ :=
  fun i => if i = 0 then m + 1 else n + 1

/-- A genuine H¹₀ sine/sine eigenmode on the unit square. -/
noncomputable def bflatSquareSineMode (m n : ℕ) :
    H10Function (openCubeSet bflatUnitSquare) :=
  ASDExplicitGamma.Cold.squareSineH10 bflatUnitSquare
    (fun i => Int.ofNat (if i = 0 then m + 1 else n + 1))

theorem bflatSquareSineMode_grad (m n : ℕ) (i : Fin 2) :
    (fun x => (bflatSquareSineMode m n).toH1Function.grad x i) =ᵐ[
        volume.restrict (openCubeSet bflatUnitSquare)]
      (fun x => cubeFreq bflatUnitSquare
        (Torus.natVec (bflatSquareModeIndex m n)) i *
        Torus.boxMode (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare)
          (Finset.univ.erase i) (Torus.natVec (bflatSquareModeIndex m n)) x) := by
  have hindex : Torus.natVec (bflatSquareModeIndex m n) =
      (fun j => Int.ofNat (if j = 0 then m + 1 else n + 1)) := by
    funext j
    simp [Torus.natVec, bflatSquareModeIndex]
  rw [hindex]
  simpa only [bflatSquareSineMode] using
    ASDExplicitGamma.Cold.squareSineH10_grad bflatUnitSquare
      (fun j => Int.ofNat (if j = 0 then m + 1 else n + 1)) i

/-- The actual Hilbert-space representative of a sine-mode gradient. -/
noncomputable def bflatSquareSineModeHilbertGradient (m n : ℕ) :
    HilbertVectorL2 (openCubeSet bflatUnitSquare) :=
  toHilbertVectorL2OfVecField
    (bflatSquareSineMode m n).toH1Function.grad_memVectorL2

private theorem bflat_boxMeasure_eq_openMeasure :
    Torus.boxMeasure (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare) =
      volume.restrict (openCubeSet bflatUnitSquare) := by
  have hvol : cubeVolume bflatUnitSquare = 1 := by
    simp [cubeVolume, bflatUnitSquare, cubeScaleFactor]
  have hnorm : normalizedCubeMeasure bflatUnitSquare =
      volume.restrict (cubeSet bflatUnitSquare) := by
    rw [normalizedCubeMeasure, cubeMeasure, hvol]
    norm_num
  calc
    Torus.boxMeasure (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare) =
        normalizedCubeMeasure bflatUnitSquare :=
      boxMeasure_eq_normalizedCubeMeasure bflatUnitSquare
    _ = volume.restrict (cubeSet bflatUnitSquare) := hnorm
    _ = volume.restrict (openCubeSet bflatUnitSquare) :=
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet bflatUnitSquare

private theorem bflat_mixed_boxNormSq (m n : ℕ) (i : Fin 2) :
    Torus.boxNormSq (Finset.univ.erase i) (bflatSquareModeIndex m n) = 1 / 4 := by
  fin_cases i <;> simp [Torus.boxNormSq, Torus.factorNormSq, bflatSquareModeIndex] <;>
    norm_num

private theorem bflat_mode_freq (m n : ℕ) (i : Fin 2) :
    cubeFreq bflatUnitSquare (Torus.natVec (bflatSquareModeIndex m n)) i =
      if i = 0 then Real.pi * (m + 1 : ℕ) else Real.pi * (n + 1 : ℕ) := by
  fin_cases i <;>
    simp [cubeFreq, bflatUnitSquare, bflatSquareModeIndex, Torus.natVec,
      cubeScaleFactor]

/-- Exact L² orthogonality and eigenvalue norm for the sine/sine Dirichlet modes. -/
theorem bflatSquareSineModeHilbertGradient_inner (m n p q : ℕ) :
    inner ℝ (bflatSquareSineModeHilbertGradient m n)
      (bflatSquareSineModeHilbertGradient p q) =
        if m = p ∧ n = q then
          cubeEig bflatUnitSquare (Torus.natVec (bflatSquareModeIndex m n)) / 4
        else 0 := by
  let hm := (bflatSquareSineMode m n).toH1Function.grad_memVectorL2
  let hp := (bflatSquareSineMode p q).toH1Function.grad_memVectorL2
  rw [bflatSquareSineModeHilbertGradient, bflatSquareSineModeHilbertGradient,
    inner_toHilbertVectorL2OfVecField_eq_integral hm hp,
    ← bflat_boxMeasure_eq_openMeasure]
  let em : Fin 2 → ℝ := fun i => cubeFreq bflatUnitSquare
    (Torus.natVec (bflatSquareModeIndex m n)) i
  let ep : Fin 2 → ℝ := fun i => cubeFreq bflatUnitSquare
    (Torus.natVec (bflatSquareModeIndex p q)) i
  let fm (i : Fin 2) : Vec 2 → ℝ := Torus.boxMode (cubeCorner bflatUnitSquare)
    (cubeScaleFactor bflatUnitSquare) (Finset.univ.erase i)
      (Torus.natVec (bflatSquareModeIndex m n))
  let fp (i : Fin 2) : Vec 2 → ℝ := Torus.boxMode (cubeCorner bflatUnitSquare)
    (cubeScaleFactor bflatUnitSquare) (Finset.univ.erase i)
      (Torus.natVec (bflatSquareModeIndex p q))
  have hgm (i : Fin 2) : (fun x => (bflatSquareSineMode m n).toH1Function.grad x i) =ᵐ[
      Torus.boxMeasure (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare)]
      (fun x => em i * fm i x) := by
    rw [bflat_boxMeasure_eq_openMeasure]
    simpa [em, fm] using bflatSquareSineMode_grad m n i
  have hgp (i : Fin 2) : (fun x => (bflatSquareSineMode p q).toH1Function.grad x i) =ᵐ[
      Torus.boxMeasure (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare)]
      (fun x => ep i * fp i x) := by
    rw [bflat_boxMeasure_eq_openMeasure]
    simpa [ep, fp] using bflatSquareSineMode_grad p q i
  have hpoint : (fun x => vecDot ((bflatSquareSineMode m n).toH1Function.grad x)
      ((bflatSquareSineMode p q).toH1Function.grad x)) =ᵐ[
        Torus.boxMeasure (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare)]
      (fun x => ∑ i : Fin 2, em i * ep i * (fm i x * fp i x)) := by
    filter_upwards [hgm 0, hgm 1, hgp 0, hgp 1] with x hm0 hm1 hp0 hp1
    simp only [vecDot, Fin.sum_univ_two]
    rw [hm0, hm1, hp0, hp1]
    ring
  rw [integral_congr_ae hpoint]
  have hterm (i : Fin 2) : Integrable (fun x =>
      em i * ep i * (fm i x * fp i x))
      (Torus.boxMeasure (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare)) := by
    dsimp [fm, fp]
    refine (Torus.integrable_of_continuous_bound
      ((Torus.continuous_boxMode _ _ _ _).mul (Torus.continuous_boxMode _ _ _ _))
      1 (fun x => ?_)).const_mul _
    rw [Pi.mul_apply, abs_mul]
    exact (mul_le_mul (Torus.abs_boxMode_le _ _ _ _ x)
      (Torus.abs_boxMode_le _ _ _ _ x) (abs_nonneg _) zero_le_one).trans
        (le_of_eq (one_mul 1))
  rw [integral_finsetSum _ (fun i hi => hterm i)]
  have hindices : bflatSquareModeIndex m n = bflatSquareModeIndex p q ↔
      m = p ∧ n = q := by
    constructor
    · intro h
      have h0 := congrFun h (0 : Fin 2)
      have h1 := congrFun h (1 : Fin 2)
      simp [bflatSquareModeIndex] at h0 h1
      exact ⟨by omega, by omega⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have hmodeint (i : Fin 2) :
      ∫ x, fm i x * fp i x ∂Torus.boxMeasure
          (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare) =
        if bflatSquareModeIndex m n = bflatSquareModeIndex p q then
          Torus.boxNormSq (Finset.univ.erase i) (bflatSquareModeIndex m n) else 0 := by
    dsimp [fm, fp]
    exact Torus.integral_boxMode_mul_boxMode (cubeCorner bflatUnitSquare)
      (cubeScaleFactor_pos' bflatUnitSquare) (Finset.univ.erase i)
      (bflatSquareModeIndex m n) (bflatSquareModeIndex p q)
  simp_rw [integral_const_mul, hmodeint, hindices]
  by_cases hmn : m = p ∧ n = q
  · rcases hmn with ⟨rfl, rfl⟩
    simp_rw [bflat_mixed_boxNormSq]
    simp [cubeEig, em, ep, bflat_mode_freq]
    ring_nf
  · simp [hmn]

theorem bflatSquareMode_eigenvalue_pos (m n : ℕ) :
    0 < cubeEig bflatUnitSquare (Torus.natVec (bflatSquareModeIndex m n)) := by
  simp [cubeEig, cubeFreq, bflatUnitSquare, bflatSquareModeIndex,
    Torus.natVec, cubeScaleFactor]
  positivity

/-- Unit L² gradient associated with a normalized square Dirichlet eigenmode. -/
noncomputable def bflatSquareSineGradientUnit (m n : ℕ) :
    HilbertVectorL2 (openCubeSet bflatUnitSquare) :=
  (2 / Real.sqrt (cubeEig bflatUnitSquare
    (Torus.natVec (bflatSquareModeIndex m n)))) •
      bflatSquareSineModeHilbertGradient m n

theorem bflatSquareSineGradientUnit_inner (m n p q : ℕ) :
    inner ℝ (bflatSquareSineGradientUnit m n) (bflatSquareSineGradientUnit p q) =
      if m = p ∧ n = q then 1 else 0 := by
  rw [bflatSquareSineGradientUnit, bflatSquareSineGradientUnit,
    inner_smul_left, inner_smul_right,
    bflatSquareSineModeHilbertGradient_inner]
  by_cases h : m = p ∧ n = q
  · rcases h with ⟨rfl, rfl⟩
    have hEig := bflatSquareMode_eigenvalue_pos m n
    have hsqrt : 0 < Real.sqrt (cubeEig bflatUnitSquare
        (Torus.natVec (bflatSquareModeIndex m n))) := Real.sqrt_pos.2 hEig
    simp only [and_self, ite_true]
    simp only [starRingEnd_apply, star_trivial]
    field_simp [ne_of_gt hsqrt]
    nlinarith only [Real.sq_sqrt hEig.le]
  · simp [h]

end ASDExplicitGamma.Model
