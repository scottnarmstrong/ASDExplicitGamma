module

public import ASDExplicitGamma.Triadic.NeumannTest
public import ASDExplicitGamma.Triadic.NeumannBlock
public import ASDExplicitGamma.Triadic.PlanarDirichletBridge
import Homogenization.Sobolev.Foundations.CoerciveH10
import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Finite Dirichlet sine polynomials and their exact spectral energy identities. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open Homogenization

local instance instPlanarDirichletCircleMeasureSpace :
    MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

namespace ASDExplicitGamma.Triadic

open Torus

variable {d : ℕ}

/-- The tensor-product Dirichlet sine mode with natural frequency `q`. -/
def cubeDirichletMode (Q : TriadicCube d) (q : Fin d → ℕ) : Vec d → ℝ :=
  boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ (natVec q)

/-- The one-coordinate derivative of a Dirichlet sine mode, with a cosine in
coordinate `j` and sines in every other coordinate. -/
def cubeDirichletMixedMode (Q : TriadicCube d) (j : Fin d) (q : Fin d → ℕ) :
    Vec d → ℝ :=
  boxMode (cubeCorner Q) (cubeScaleFactor Q) (Finset.univ.erase j) (natVec q)

/-- The finite gradient of a Dirichlet sine polynomial. -/
def dirichletTestField (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j : Fin d) (x : Vec d) : ℝ :=
  ∑ q ∈ S, (β q * cubeFreq Q (natVec q) j) * cubeDirichletMixedMode Q j q x

/-- The sine/cosine mode appearing after two derivatives of a Dirichlet sine
polynomial. -/
def dirichletHessSet (i j : Fin d) : Finset (Fin d) :=
  if i = j then Finset.univ else (Finset.univ.erase i).erase j

/-- The coefficient in the `i`-derivative of the `j`-component of a finite
Dirichlet gradient. -/
def dirichletHessCoef (Q : TriadicCube d) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) (q : Fin d → ℕ) : ℝ :=
  β q * cubeFreq Q (natVec q) j *
    ((if i = j then -1 else 1) * cubeFreq Q (natVec q) i)

/-- The finite Hessian entry of the Dirichlet sine polynomial. -/
def dirichletTestHess (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j i : Fin d) (x : Vec d) : ℝ :=
  ∑ q ∈ S, dirichletHessCoef Q β j i q *
    boxMode (cubeCorner Q) (cubeScaleFactor Q) (dirichletHessSet i j) (natVec q) x

/-- Smoothness of a single tensor-product box mode. -/
theorem contDiff_cubeDirichletMode (Q : TriadicCube d) (O : Finset (Fin d))
    (p : Fin d → ℤ) {m : ℕ∞} :
    ContDiff ℝ m (Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q) O p) := by
  show ContDiff ℝ m (fun y : Fin d → ℝ =>
    ∏ i, Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) O p i (y i))
  refine contDiff_prod (t := Finset.univ)
    (f := fun i (y : Fin d → ℝ) =>
      Torus.modeFactor (cubeCorner Q) (cubeScaleFactor Q) O p i (y i)) fun i _ => ?_
  exact (Torus.contDiff_modeFactor _ _ _ _ i).comp (contDiff_apply ℝ ℝ i)

/-- Smoothness of the finite sine/cosine polynomial test field. -/
theorem contDiff_dirichletTestField (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j : Fin d) {m : ℕ∞} :
    ContDiff ℝ m (dirichletTestField Q S β j) := by
  unfold dirichletTestField cubeDirichletMixedMode
  refine ContDiff.sum fun q hq => ?_
  exact contDiff_const.mul
    (contDiff_cubeDirichletMode Q (Finset.univ.erase j) (natVec q) (m := m))

/-- The finite Dirichlet gradient field, viewed as an `H¹` function. -/
noncomputable def dirichletTestFieldH1 (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j : Fin d) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_dirichletTestField Q S β j (m := 1))

@[simp] theorem dirichletTestFieldH1_toFun (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ) (j : Fin d) :
    (dirichletTestFieldH1 Q S β j).toFun = dirichletTestField Q S β j := rfl

/-- The line derivative of the finite Dirichlet gradient is its Hessian entry. -/
theorem hasDerivAt_dirichletTestField (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) (x : Vec d) :
    HasDerivAt (fun t => dirichletTestField Q S β j (Function.update x i t))
      (dirichletTestHess Q S β j i x) (x i) := by
  have h := HasDerivAt.fun_sum (u := S) fun q _ =>
    (hasDerivAt_boxMode_update (cubeCorner Q) (cubeScaleFactor Q)
      (Finset.univ.erase j) (natVec q) i x).const_mul
      (β q * cubeFreq Q (natVec q) j)
  unfold dirichletTestField
  refine h.congr_deriv ?_
  unfold dirichletTestHess
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold dirichletHessCoef dirichletHessSet cubeFreq
  by_cases hij : i = j
  · subst hij
    simp only [Finset.notMem_erase, ite_false, ite_true]
    rw [Finset.insert_erase (Finset.mem_univ i)]
    ring
  · have hji : j ≠ i := Ne.symm hij
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
    simp only [hi, ite_true, hij, ite_false]
    have hsets : (Finset.univ.erase j).erase i = (Finset.univ.erase i).erase j := by
      ext k
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact and_comm
    rw [hsets]
    ring

/-- The coordinate derivative represented by the finite test Hessian. -/
theorem fderiv_dirichletTestField_apply (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) (x : Vec d) :
    (fderiv ℝ (dirichletTestField Q S β j) x) (basisVec i) =
      dirichletTestHess Q S β j i x := by
  have hf : DifferentiableAt ℝ (dirichletTestField Q S β j) x :=
    ((contDiff_dirichletTestField Q S β j (m := 1)).differentiable (by simp)) x
  have hline : HasDerivAt (fun t => Function.update x i t)
      (basisVec i) (x i) := by
    convert (hasFDerivAt_update x (x i)).hasDerivAt using 1
    ext k
    by_cases hki : k = i <;> simp [basisVec, hki]
  have hf' : DifferentiableAt ℝ (dirichletTestField Q S β j)
      (Function.update x i (x i)) := by simpa using hf
  have hchain := fderiv_comp_deriv (l := dirichletTestField Q S β j)
    (f := fun t => Function.update x i t) (x := x i) hf' hline.differentiableAt
  have hchain' := hchain
  rw [hline.deriv, Function.update_eq_self] at hchain'
  change deriv (fun t => dirichletTestField Q S β j (Function.update x i t))
      (x i) = _ at hchain'
  rw [(hasDerivAt_dirichletTestField Q S β j i x).deriv] at hchain'
  exact hchain'.symm

/-- The gradient of the bundled finite test field is its explicitly computed
finite Hessian. -/
theorem dirichletTestFieldH1_grad (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) (x : Vec d) :
    (dirichletTestFieldH1 Q S β j).grad x i = dirichletTestHess Q S β j i x := by
  exact fderiv_dirichletTestField_apply Q S β j i x

/-- The exact `L²` energy of a finite Dirichlet gradient component. -/
theorem energy_dirichletTestField (Q : TriadicCube d) (S : Finset (Fin d → ℕ))
    (β : (Fin d → ℕ) → ℝ) (j : Fin d)
    (hS : ∀ q ∈ S, ∀ i, q i ≠ 0) :
    energy Q (dirichletTestField Q S β j) =
      ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 / modeMult q := by
  rw [energy_eq_integral_sq, ← boxMeasure_eq_normalizedCubeMeasure]
  unfold dirichletTestField cubeDirichletMixedMode
  rw [integral_sq_sum_boxMode _ (cubeScaleFactor_pos' Q)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [boxNormSq_eq_inv_modeMult _ q (fun k hk => hS q hq k)]
  simp only [div_eq_mul_inv]
  ring

/-- Summing the finite test-field component energies gives the Dirichlet
eigenvalue weight. -/
theorem sum_energy_dirichletTestField (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (hS : ∀ q ∈ S, ∀ i, q i ≠ 0) :
    ∑ j, energy Q (dirichletTestField Q S β j) =
      ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q := by
  have heq : ∀ j, energy Q (dirichletTestField Q S β j) =
      ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 / modeMult q :=
    fun j => energy_dirichletTestField Q S β j hS
  simp_rw [heq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  unfold cubeEig
  rw [← Finset.sum_div, ← Finset.mul_sum]

/-- The exact `L²` energy of a finite Dirichlet Hessian entry. -/
theorem energy_dirichletTestHess (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (j i : Fin d) (hS : ∀ q ∈ S, ∀ k, q k ≠ 0) :
    energy Q (dirichletTestHess Q S β j i) =
      ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
        cubeFreq Q (natVec q) i ^ 2 / modeMult q := by
  rw [energy_eq_integral_sq, ← boxMeasure_eq_normalizedCubeMeasure]
  unfold dirichletTestHess
  rw [integral_sq_sum_boxMode _ (cubeScaleFactor_pos' Q)]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hcoef : dirichletHessCoef Q β j i q ^ 2 =
      β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 * cubeFreq Q (natVec q) i ^ 2 := by
    unfold dirichletHessCoef
    split_ifs <;> ring
  rw [hcoef, boxNormSq_eq_inv_modeMult _ q (fun k hk => hS q hq k)]
  simp only [div_eq_mul_inv]

/-- Summing over both Hessian indices gives the exact Laplacian energy. -/
theorem sum_sum_energy_dirichletTestHess (Q : TriadicCube d)
    (S : Finset (Fin d → ℕ)) (β : (Fin d → ℕ) → ℝ)
    (hS : ∀ q ∈ S, ∀ k, q k ≠ 0) :
    ∑ j, ∑ i, energy Q (dirichletTestHess Q S β j i) =
      ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
  have heq : ∀ j i, energy Q (dirichletTestHess Q S β j i) =
      ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
        cubeFreq Q (natVec q) i ^ 2 / modeMult q :=
    fun j i => energy_dirichletTestHess Q S β j i hS
  simp_rw [heq]
  have key : ∀ q, ∑ j, ∑ i, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
      cubeFreq Q (natVec q) i ^ 2 / modeMult q =
        β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
    intro q
    unfold cubeEig
    rw [sq (∑ j, cubeFreq Q (natVec q) j ^ 2), Finset.sum_mul_sum,
      Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  calc
    ∑ j, ∑ i, ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
          cubeFreq Q (natVec q) i ^ 2 / modeMult q
        = ∑ j, ∑ q ∈ S, ∑ i, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
          cubeFreq Q (natVec q) i ^ 2 / modeMult q :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ q ∈ S, ∑ j, ∑ i, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 *
          cubeFreq Q (natVec q) i ^ 2 / modeMult q := Finset.sum_comm
    _ = ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q :=
          Finset.sum_congr rfl fun q _ => key q

/-- Every planar Dirichlet mode has eigenvalue at least the first cube
eigenvalue `2π²/R²`. -/
theorem planar_cubeEig_lower_of_nonzero (Q : TriadicCube 2)
    (q : Fin 2 → ℕ) (hq : ∀ i, q i ≠ 0) :
    2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2 ≤ cubeEig Q (natVec q) := by
  have hR : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have hfreq : ∀ i : Fin 2,
      (Real.pi / cubeScaleFactor Q) ^ 2 ≤ cubeFreq Q (natVec q) i ^ 2 := by
    intro i
    have hqi : (1 : ℝ) ≤ (q i : ℝ) := by
      have hnat : 1 ≤ q i := Nat.one_le_iff_ne_zero.mpr (hq i)
      exact_mod_cast hnat
    have hle : Real.pi / cubeScaleFactor Q ≤ cubeFreq Q (natVec q) i := by
      unfold cubeFreq natVec
      push_cast
      have hmul : Real.pi ≤ Real.pi * (q i : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hqi Real.pi_pos.le]
      exact (div_le_div_of_nonneg_right hmul hR.le)
    apply (sq_le_sq₀ (by positivity) (by
      unfold cubeFreq natVec
      positivity)).2 hle
  have hsum : ∑ i : Fin 2, (Real.pi / cubeScaleFactor Q) ^ 2 ≤
      cubeEig Q (natVec q) := by
    unfold cubeEig
    exact Finset.sum_le_sum fun i _ => hfreq i
  have hsum' : ∑ i : Fin 2, (Real.pi / cubeScaleFactor Q) ^ 2 =
      2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2 := by
    simp [div_pow]
    ring
  rw [← hsum']
  exact hsum

/-- The positive Haar norm of a finite planar Dirichlet gradient is controlled
by its Laplacian energy with the sharp `c_D` coefficient. -/
theorem vectorPositiveHaarNorm_dirichletTestField_sq_le
    (Q : TriadicCube 2) (S : Finset (Fin 2 → ℕ))
    (β : (Fin 2 → ℕ) → ℝ) (hS : ∀ q ∈ S, ∀ i, q i ≠ 0) :
    vectorPositiveHaarNorm Q (fun x j => dirichletTestField Q S β j x) ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
  have hpos : ∀ j : Fin 2,
      positiveHaarNorm Q (dirichletTestField Q S β j) ^ 2 ≤
        energy Q (dirichletTestField Q S β j) +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            ∑ i : Fin 2, energy Q (dirichletTestHess Q S β j i) := by
    intro j
    have hf : MemLp (dirichletTestField Q S β j) 2 (normalizedCubeMeasure Q) :=
      (dirichletTestFieldH1 Q S β j).memL2_normalizedCubeMeasure
    have hG : ∀ i : Fin 2,
        MemLp (fun x => dirichletTestHess Q S β j i x) 2
          (normalizedCubeMeasure Q) := by
      intro i
      simpa only [dirichletTestFieldH1_grad] using
        (dirichletTestFieldH1 Q S β j).grad_memL2_normalizedCubeMeasure i
    have hw : HasWeakGradientOn (openCubeSet Q) (dirichletTestField Q S β j)
        (fun x i => dirichletTestHess Q S β j i x) := by
      have h := (dirichletTestFieldH1 Q S β j).hasWeakGradient
      have hgrad : (dirichletTestFieldH1 Q S β j).grad =
          fun x i => dirichletTestHess Q S β j i x := by
        funext x i
        exact dirichletTestFieldH1_grad Q S β j i x
      rw [hgrad] at h
      exact h
    exact positiveHaarNorm_sq_le_l2_add_gradient Q hf hG hw
  have hsumPos := Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) => hpos j
  rw [vectorPositiveHaarNorm_sq]
  calc
    ∑ j : Fin 2, positiveHaarNorm Q (dirichletTestField Q S β j) ^ 2 ≤
        ∑ j : Fin 2,
          (energy Q (dirichletTestField Q S β j) +
            cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
              ∑ i : Fin 2, energy Q (dirichletTestHess Q S β j i)) := hsumPos
    _ = ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
        calc
          ∑ j : Fin 2,
              (energy Q (dirichletTestField Q S β j) +
                cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
                  ∑ i : Fin 2, energy Q (dirichletTestHess Q S β j i))
              = (∑ j : Fin 2, energy Q (dirichletTestField Q S β j)) +
                  cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
                    ∑ j : Fin 2, ∑ i : Fin 2,
                      energy Q (dirichletTestHess Q S β j i) := by
                    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = _ := by rw [sum_energy_dirichletTestField Q S β hS,
            sum_sum_energy_dirichletTestHess Q S β hS]
    _ ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
          ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
        have heig : ∀ q ∈ S,
            2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2 ≤ cubeEig Q (natVec q) :=
          fun q hq => planar_cubeEig_lower_of_nonzero Q q (hS q hq)
        have hterm : ∀ q ∈ S,
            β q ^ 2 * cubeEig Q (natVec q) / modeMult q ≤
              (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2)) *
                (β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
          intro q hq
          have hm : 0 < modeMult q := modeMult_pos q
          have hb : 0 ≤ β q ^ 2 := sq_nonneg _
          have hscale : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
          have he : 0 < cubeEig Q (natVec q) := lt_of_lt_of_le
            (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2)
            (heig q hq)
          have hcoeff : 0 ≤ β q ^ 2 / modeMult q := div_nonneg hb hm.le
          have hden : 0 < 2 * Real.pi ^ 2 := by positivity
          have hR2 : 0 < cubeScaleFactor Q ^ 2 := pow_pos hscale _
          have hmulEig : 2 * Real.pi ^ 2 ≤ cubeScaleFactor Q ^ 2 *
              cubeEig Q (natVec q) :=
            (div_le_iff₀ hR2).mp (heig q hq) |>.trans_eq (by ring)
          have hbase : 1 ≤ cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2) *
              cubeEig Q (natVec q) := by
            calc
              1 ≤ (cubeScaleFactor Q ^ 2 * cubeEig Q (natVec q)) /
                  (2 * Real.pi ^ 2) := (one_le_div hden).2 hmulEig
              _ = cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2) *
                    cubeEig Q (natVec q) := by ring
          have hmul := mul_le_mul_of_nonneg_left hbase hcoeff
          have heq : β q ^ 2 * cubeEig Q (natVec q) / modeMult q =
              (β q ^ 2 / modeMult q) * cubeEig Q (natVec q) := by ring
          have heq' : (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2)) *
              (β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) =
              (β q ^ 2 / modeMult q) * cubeEig Q (natVec q) *
                (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2) * cubeEig Q (natVec q)) := by ring
          rw [heq, heq']
          have hmul' := mul_le_mul_of_nonneg_right hmul he.le
          nlinarith [hmul']
        have hsumterms :
            (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q) ≤
              (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2)) *
                ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
          calc
            (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q) ≤
                ∑ q ∈ S, (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2)) *
                  (β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) :=
              Finset.sum_le_sum hterm
            _ = (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2)) *
                  ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
              rw [← Finset.mul_sum]
        have hcD : planarCD ^ 2 = planarC1 ^ 2 + 1 / (2 * Real.pi ^ 2) := planarCD_sq
        have hnonneg : 0 ≤ ∑ q ∈ S,
            β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
          apply Finset.sum_nonneg
          intro q hq
          have hm : 0 < modeMult q := modeMult_pos q
          positivity
        have hR : 0 ≤ cubeScaleFactor Q ^ 2 := sq_nonneg _
        have hC : 0 ≤ planarC1 ^ 2 := sq_nonneg _
        calc
          (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q) +
              cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
                ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q
              ≤ (cubeScaleFactor Q ^ 2 / (2 * Real.pi ^ 2)) *
                  ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q +
                cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
                  ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
                    exact add_le_add hsumterms (le_refl _)
          _ = cubeScaleFactor Q ^ 2 * (planarC1 ^ 2 + 1 / (2 * Real.pi ^ 2)) *
                ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by ring
          _ = cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
                ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q := by
                  rw [hcD]

/-- The signed-frequency coefficient of `f` against a two-dimensional sine
mode on `Q`. -/
noncomputable def dirichletFourierCoeff (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (p : Fin 2 → ℤ) : ℝ :=
  ∫ x, Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p x * f x ∂
    Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q)

/-- Integration by parts against a compactly supported smooth function turns
the mixed cosine-sine mode into the Dirichlet sine mode. -/
theorem integral_compactDeriv_mul_dirichletMixed (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ openCubeSet Q) (j : Fin 2) (q : Fin 2 → ℕ) :
    ∫ x, (fderiv ℝ f x) (basisVec j) * cubeDirichletMixedMode Q j q x
        ∂normalizedCubeMeasure Q =
      cubeFreq Q (natVec q) j *
        dirichletFourierCoeff Q f (natVec q) := by
  let m : Vec 2 → ℝ := cubeDirichletMixedMode Q j q
  let s : Vec 2 → ℝ := cubeDirichletMode Q q
  let D : Vec 2 → ℝ := fun x => (fderiv ℝ f x) (basisVec j)
  have hm : Continuous m := by
    dsimp [m, cubeDirichletMixedMode]
    exact Torus.continuous_boxMode _ _ _ _
  have hsC : Continuous s := by
    dsimp [s, cubeDirichletMode]
    exact Torus.continuous_boxMode _ _ _ _
  have hD : Continuous D := by
    dsimp [D]
    simpa using (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport D := by
    dsimp [D]
    exact hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hmodeDeriv : ∀ x, (fderiv ℝ m x) (basisVec j) =
      -cubeFreq Q (natVec q) j * s x := by
    intro x
    have hline := Torus.hasDerivAt_boxMode_update (cubeCorner Q) (cubeScaleFactor Q)
      (Finset.univ.erase j) (natVec q) j x
    have hline' : HasDerivAt (fun t => m (Function.update x j t))
        (-cubeFreq Q (natVec q) j * s x) (x j) := by
      simpa [m, s, cubeDirichletMixedMode, cubeDirichletMode, cubeFreq,
        Finset.notMem_erase, Finset.insert_erase (Finset.mem_univ j)] using hline
    have hdiff : DifferentiableAt ℝ m x :=
      ((contDiff_cubeDirichletMode Q (Finset.univ.erase j) (natVec q)
        (m := 1)).differentiable (by simp)) x
    have hupdate : HasDerivAt (fun t : ℝ => Function.update x j t)
        (basisVec j) (x j) := by
      convert (hasFDerivAt_update x (x j)).hasDerivAt using 1
      ext k
      by_cases hkj : k = j <;> simp [basisVec, hkj]
    have hdiff' : DifferentiableAt ℝ m (Function.update x j (x j)) := by
      simpa using hdiff
    have hchain := fderiv_comp_deriv (l := m)
      (f := fun t => Function.update x j t) (x := x j) hdiff' hupdate.differentiableAt
    have hchain' := hchain
    rw [hupdate.deriv, Function.update_eq_self] at hchain'
    change deriv (fun t => m (Function.update x j t)) (x j) = _ at hchain'
    rw [hline'.deriv] at hchain'
    exact hchain'.symm
  have hInt₁ : Integrable (fun x => D x * m x) volume :=
    (hD.mul hm).integrable_of_hasCompactSupport (hDc.mul_right)
  have hInt₂ : Integrable (fun x => f x * (fun x => (fderiv ℝ m x) (basisVec j)) x)
      volume := by
    have hderiv : Continuous (fun x => (fderiv ℝ m x) (basisVec j)) := by
      dsimp [m, cubeDirichletMixedMode]
      exact ((contDiff_cubeDirichletMode Q (Finset.univ.erase j) (natVec q)
        (m := 1)).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hf.continuous.mul hderiv).integrable_of_hasCompactSupport hfc.mul_right
  have hInt₃ : Integrable (fun x => f x * m x) volume :=
    (hf.continuous.mul hm).integrable_of_hasCompactSupport hfc.mul_right
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := f) (g := m) (v := basisVec j)
    hInt₁ hInt₂ hInt₃
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => ((contDiff_cubeDirichletMode Q (Finset.univ.erase j) (natVec q)
      (m := 1)).differentiable (by simp)) x)
  have hreplace : (fun x => f x * (fderiv ℝ m x) (basisVec j)) =
      fun x => -cubeFreq Q (natVec q) j * (s x * f x) := by
    funext x
    rw [hmodeDeriv x]
    ring
  have hleft : ∫ x, f x * (fderiv ℝ m x) (basisVec j) =
      -cubeFreq Q (natVec q) j * ∫ x, s x * f x := by
    calc
      ∫ x, f x * (fderiv ℝ m x) (basisVec j) =
          ∫ x, -cubeFreq Q (natVec q) j * (s x * f x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => congrFun hreplace x)
      _ = -cubeFreq Q (natVec q) j * ∫ x, s x * f x := integral_const_mul _ _
  have hIBP' : ∫ x, f x * (fderiv ℝ m x) (basisVec j) = -∫ x, D x * m x := by
    simpa [D] using hIBP
  have hfull : ∫ x, D x * m x =
      cubeFreq Q (natVec q) j * ∫ x, s x * f x := by
    rw [hleft] at hIBP'
    linarith
  have hzero₁ : ∀ x ∉ openCubeSet Q, D x * m x = 0 := by
    intro x hx
    have hnot : x ∉ tsupport f := fun h => hx (hsupp h)
    have hfderiv : (fderiv ℝ f x) (basisVec j) = 0 := by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
      simp
    simp [D, hfderiv]
  have hzero₂ : ∀ x ∉ openCubeSet Q, s x * f x = 0 := by
    intro x hx
    have hnot : x ∉ tsupport f := fun h => hx (hsupp h)
    have hfzero : f x = 0 := by
      by_contra hne
      have hsupport : x ∈ Function.support f := Function.mem_support.mpr hne
      have hclosure : x ∈ closure (Function.support f) := subset_closure hsupport
      exact hnot hclosure
    simp [hfzero]
  have hnorm₁ : ∫ x, D x * m x ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ * ∫ x, D x * m x := by
    rw [integral_normalized_eq_open Q]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero₁]
  have hnorm₂ : ∫ x, s x * f x ∂normalizedCubeMeasure Q =
      (cubeVolume Q)⁻¹ * ∫ x, s x * f x := by
    rw [integral_normalized_eq_open Q]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero₂]
  have hcoeff : dirichletFourierCoeff Q f (natVec q) =
      ∫ x, s x * f x ∂normalizedCubeMeasure Q := by
    rw [dirichletFourierCoeff, ← boxMeasure_eq_normalizedCubeMeasure Q]
    rfl
  change ∫ x, D x * m x ∂normalizedCubeMeasure Q =
    cubeFreq Q (natVec q) j * dirichletFourierCoeff Q f (natVec q)
  rw [hcoeff, hnorm₁, hnorm₂, hfull]
  ring

/-- The compact-support integration-by-parts identity extends to an `H10`
function by its defining smooth compactly supported approximants. -/
theorem integral_h10Deriv_mul_dirichletMixed (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (j : Fin 2) (q : Fin 2 → ℕ) :
    ∫ x, (u.toH1Function.grad x j) * cubeDirichletMixedMode Q j q x
        ∂normalizedCubeMeasure Q =
      cubeFreq Q (natVec q) j *
        dirichletFourierCoeff Q u.toH1Function.toFun (natVec q) := by
  let U := openCubeSet Q
  let m : Vec 2 → ℝ := cubeDirichletMixedMode Q j q
  let s : Vec 2 → ℝ := cubeDirichletMode Q q
  let D : ℕ → Vec 2 → ℝ := fun n x =>
    (fderiv ℝ (u.approx n) x) (basisVec j)
  have hmNorm : MemLp m 2 (normalizedCubeMeasure Q) := by
    dsimp [m, cubeDirichletMixedMode]
    exact memLp_of_continuous_bound
      (Torus.continuous_boxMode (cubeCorner Q) (cubeScaleFactor Q)
        (Finset.univ.erase j) (natVec q)) _
      (fun x => Torus.abs_boxMode_le (cubeCorner Q) (cubeScaleFactor Q)
        (Finset.univ.erase j) (natVec q) x) 2
  have hm : MemScalarL2 U m := by
    simpa [MemScalarL2, volumeMeasureOn, MemL2On] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hmNorm
  have hsNorm : MemLp s 2 (normalizedCubeMeasure Q) := by
    dsimp [s, cubeDirichletMode]
    exact memLp_of_continuous_bound
      (Torus.continuous_boxMode (cubeCorner Q) (cubeScaleFactor Q)
        Finset.univ (natVec q)) _
      (fun x => Torus.abs_boxMode_le (cubeCorner Q) (cubeScaleFactor Q)
        Finset.univ (natVec q) x) 2
  have hs : MemScalarL2 U s := by
    simpa [MemScalarL2, volumeMeasureOn, MemL2On] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hsNorm
  have happ : ∀ n, MemScalarL2 U (u.approx n) := by
    intro n
    simpa [MemScalarL2, volumeMeasureOn] using
      ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
        (u.approx_hasCompactSupport n)).restrict U
  have hDapp : ∀ n, MemScalarL2 U (D n) := by
    intro n
    have hcont : Continuous (D n) := by
      dsimp [D]
      simpa using
        ((u.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    have hcompact : HasCompactSupport (D n) := by
      dsimp [D]
      exact (u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec j)
    simpa [MemScalarL2, volumeMeasureOn] using
      (hcont.memLp_of_hasCompactSupport hcompact).restrict U
  have hu : MemScalarL2 U u.toH1Function.toFun := u.toH1Function.memL2
  have hgrad : MemScalarL2 U (fun x => u.toH1Function.grad x j) :=
    u.toH1Function.grad_memL2 j
  have happConv : Tendsto (fun n => toScalarL2 (happ n)) atTop
      (nhds (toScalarL2 hu)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm happ hu u.tendsto_approx
  have hDappConv : Tendsto (fun n => toScalarL2 (hDapp n)) atTop
      (nhds (toScalarL2 hgrad)) := by
    refine tendsto_toScalarL2_of_tendsto_eLpNorm hDapp hgrad ?_
    simpa [D] using u.tendsto_approx_grad j
  have hCoeffOpen : Tendsto
      (fun n => ∫ x in U, s x * u.approx n x ∂volume) atTop
      (nhds (∫ x in U, s x * u.toH1Function.toFun x ∂volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 hs happ hu happConv
  have hDerivOpen : Tendsto
      (fun n => ∫ x in U, m x * D n x ∂volume) atTop
      (nhds (∫ x in U, m x * u.toH1Function.grad x j ∂volume)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 hm hDapp hgrad hDappConv
  have hCoeffNorm : Tendsto
      (fun n => dirichletFourierCoeff Q (u.approx n) (natVec q)) atTop
      (nhds (dirichletFourierCoeff Q u.toH1Function.toFun (natVec q))) := by
    have hseq : (fun n => dirichletFourierCoeff Q (u.approx n) (natVec q)) =
        fun n => (cubeVolume Q)⁻¹ * ∫ x in U, s x * u.approx n x ∂volume := by
      funext n
      rw [dirichletFourierCoeff, boxMeasure_eq_normalizedCubeMeasure Q,
        integral_normalized_eq_open Q]
      simp [U, s, cubeDirichletMode]
    have hlim : dirichletFourierCoeff Q u.toH1Function.toFun (natVec q) =
        (cubeVolume Q)⁻¹ * ∫ x in U, s x * u.toH1Function.toFun x ∂volume := by
      rw [dirichletFourierCoeff, boxMeasure_eq_normalizedCubeMeasure Q,
        integral_normalized_eq_open Q]
      simp [U, s, cubeDirichletMode]
    rw [hseq, hlim]
    exact hCoeffOpen.const_mul (cubeVolume Q)⁻¹
  have hDerivNorm : Tendsto
      (fun n => ∫ x, D n x * m x ∂normalizedCubeMeasure Q) atTop
      (nhds (∫ x, u.toH1Function.grad x j * m x ∂normalizedCubeMeasure Q)) := by
    have hseq : (fun n => ∫ x, D n x * m x ∂normalizedCubeMeasure Q) =
        fun n => (cubeVolume Q)⁻¹ * ∫ x in U, m x * D n x ∂volume := by
      funext n
      rw [integral_normalized_eq_open Q]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring
    have hlim : (∫ x, u.toH1Function.grad x j * m x ∂normalizedCubeMeasure Q) =
        (cubeVolume Q)⁻¹ * ∫ x in U, m x * u.toH1Function.grad x j ∂volume := by
      rw [integral_normalized_eq_open Q]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hseq, hlim]
    exact hDerivOpen.const_mul (cubeVolume Q)⁻¹
  have hidentity : ∀ n,
      (∫ x, D n x * m x ∂normalizedCubeMeasure Q) =
        cubeFreq Q (natVec q) j * dirichletFourierCoeff Q (u.approx n) (natVec q) := by
    intro n
    simpa [D, euclideanCoordDeriv, m, cubeDirichletMixedMode,
      dirichletFourierCoeff, cubeDirichletMode] using
      (integral_compactDeriv_mul_dirichletMixed Q (u.approx n)
        (u.approx_smooth n) (u.approx_hasCompactSupport n)
        (u.approx_support_subset n) j q)
  have hconst : Tendsto (fun _ : ℕ => cubeFreq Q (natVec q) j) atTop
      (nhds (cubeFreq Q (natVec q) j)) := tendsto_const_nhds
  have hRhs : Tendsto
      (fun n => cubeFreq Q (natVec q) j * dirichletFourierCoeff Q (u.approx n) (natVec q))
      atTop (nhds (cubeFreq Q (natVec q) j *
        dirichletFourierCoeff Q u.toH1Function.toFun (natVec q))) := hconst.mul hCoeffNorm
  have hLhs := hDerivNorm.congr' (Filter.Eventually.of_forall hidentity)
  have hlim := tendsto_nhds_unique hLhs hRhs
  change (∫ x, u.toH1Function.grad x j * m x ∂normalizedCubeMeasure Q) =
    cubeFreq Q (natVec q) j * dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)
  exact hlim

/-- Pairing a scalar field with one component of a finite Dirichlet test field
distributes over its frequencies. -/
theorem pairing_dirichletTestField (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ) (j : Fin 2)
    {h : Vec 2 → ℝ} (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    pairing Q h (dirichletTestField Q S β j) =
      ∑ q ∈ S, (β q * cubeFreq Q (natVec q) j) *
        ∫ x, cubeDirichletMixedMode Q j q x * h x ∂normalizedCubeMeasure Q := by
  unfold pairing dirichletTestField
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp_rw [cubeDirichletMixedMode]
  have hint : ∀ q ∈ S, Integrable (fun x => h x *
      ((β q * cubeFreq Q (natVec q) j) *
        Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q)
          (Finset.univ.erase j) (natVec q) x)) (normalizedCubeMeasure Q) := by
    intro q hq
    have hmode := memLp_mode_mul hh
      (Torus.continuous_boxMode (cubeCorner Q) (cubeScaleFactor Q)
        (Finset.univ.erase j) (natVec q))
      (Torus.abs_boxMode_le (cubeCorner Q) (cubeScaleFactor Q)
        (Finset.univ.erase j) (natVec q))
    refine (hmode.const_mul (β q * cubeFreq Q (natVec q) j)).congr
      (Eventually.of_forall fun x => ?_)
    ring
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun q hq => ?_
  calc
    ∫ x, h x * ((β q * cubeFreq Q (natVec q) j) *
        Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q)
          (Finset.univ.erase j) (natVec q) x) ∂normalizedCubeMeasure Q =
      ∫ x, (β q * cubeFreq Q (natVec q) j) *
        (cubeDirichletMixedMode Q j q x * h x) ∂normalizedCubeMeasure Q := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            simp [cubeDirichletMixedMode]
            ring
    _ = (β q * cubeFreq Q (natVec q) j) *
        ∫ x, cubeDirichletMixedMode Q j q x * h x ∂normalizedCubeMeasure Q :=
          integral_const_mul _ _

/-- The spectral Poisson test fields control every finite positive-frequency
Dirichlet coefficient sum by the weak Haar norm of the gradient. -/
theorem finite_dirichlet_weakHaar_bound (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q))
    (S : Finset (Fin 2 → ℕ)) (hS : ∀ q ∈ S, ∀ i, q i ≠ 0) :
    ∑ q ∈ S, modeMult q *
        dirichletFourierCoeff Q u.toH1Function.toFun (natVec q) ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) ^ 2 := by
  let c : (Fin 2 → ℕ) → ℝ := fun q =>
    dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)
  let β : (Fin 2 → ℕ) → ℝ := fun q =>
    modeMult q * c q / cubeEig Q (natVec q)
  let G : Vec 2 → Fin 2 → ℝ := fun x i => u.toH1Function.grad x i
  let F : Vec 2 → Fin 2 → ℝ := fun x i => dirichletTestField Q S β i x
  have hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    simpa [G] using u.toH1Function.grad_memL2_normalizedCubeMeasure i
  have hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    simpa [F] using (dirichletTestFieldH1 Q S β i).memL2_normalizedCubeMeasure
  have hFpos : ∀ i, Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i))) := by
    intro i
    let hu := dirichletTestFieldH1 Q S β i
    have hgrad : hu.grad = fun x k => dirichletTestHess Q S β i k x := by
      funext x k
      simpa [hu] using dirichletTestFieldH1_grad Q S β i k x
    have hweak' := hu.hasWeakGradient
    rw [hgrad] at hweak'
    have hweak : HasWeakGradientOn (openCubeSet Q)
        (dirichletTestField Q S β i)
        (fun x k => dirichletTestHess Q S β i k x) := by
      simpa [hu, dirichletTestFieldH1_toFun] using hweak'
    have hhess : ∀ k, MemLp (fun x => dirichletTestHess Q S β i k x) 2
        (normalizedCubeMeasure Q) := by
      intro k
      simpa [hu, dirichletTestFieldH1_grad] using hu.grad_memL2_normalizedCubeMeasure k
    exact positiveHaarIncrementSeries_summable Q
      (by simpa [F, hu, dirichletTestFieldH1_toFun] using hu.memL2_normalizedCubeMeasure)
      hhess hweak
  have hdualBase : |vectorPairing Q F G| ≤
      vectorPositiveHaarNorm Q F * vectorWeakHaarNorm Q G :=
    abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
      Q hF hG hFpos
  have hFG : vectorPairing Q G F = vectorPairing Q F G := by
    unfold vectorPairing
    apply Finset.sum_congr rfl
    intro i hi
    exact pairing_comm Q (fun x => G x i) (fun x => F x i)
  have hdual : |vectorPairing Q G F| ≤
      vectorPositiveHaarNorm Q F * vectorWeakHaarNorm Q G := by
    rw [hFG]
    exact hdualBase
  have hpair : vectorPairing Q G F =
      ∑ q ∈ S, modeMult q * c q ^ 2 := by
    unfold vectorPairing F
    rw [Finset.sum_congr rfl fun j _ => pairing_dirichletTestField Q S β j (hG j)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hcoef : ∀ j,
        ∫ x, cubeDirichletMixedMode Q j q x * G x j ∂normalizedCubeMeasure Q =
          cubeFreq Q (natVec q) j * c q := by
      intro j
      rw [show (fun x => cubeDirichletMixedMode Q j q x * G x j) =
        fun x => u.toH1Function.grad x j * cubeDirichletMixedMode Q j q x by
          funext x
          simp [G]
          ring]
      simpa [c] using integral_h10Deriv_mul_dirichletMixed Q u j q
    have hsum : ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
          (cubeFreq Q (natVec q) j * c q) = β q * c q * cubeEig Q (natVec q) := by
      calc
        ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
            (cubeFreq Q (natVec q) j * c q) =
          β q * c q * ∑ j : Fin 2, cubeFreq Q (natVec q) j ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = β q * c q * cubeEig Q (natVec q) := by rw [cubeEig]
    have hEigNonzero : cubeEig Q (natVec q) ≠ 0 := by
      have hpos := planar_cubeEig_lower_of_nonzero Q q (hS q hq)
      have hbase : 0 < 2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2 :=
        div_pos (by positivity) (sq_pos_of_pos (cubeScaleFactor_pos' Q))
      exact ne_of_gt (lt_of_lt_of_le hbase hpos)
    calc
      ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
          ∫ x, cubeDirichletMixedMode Q j q x * G x j ∂normalizedCubeMeasure Q =
        β q * c q * cubeEig Q (natVec q) := by
          calc
            _ = ∑ j : Fin 2, (β q * cubeFreq Q (natVec q) j) *
                (cubeFreq Q (natVec q) j * c q) := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [hcoef j]
            _ = β q * c q * cubeEig Q (natVec q) := hsum
      _ = modeMult q * c q ^ 2 := by
        dsimp [β]
        field_simp [hEigNonzero]
        
  have hA : 0 ≤ ∑ q ∈ S, modeMult q * c q ^ 2 := by
    apply Finset.sum_nonneg
    intro q hq
    exact mul_nonneg (modeMult_pos q).le (sq_nonneg _)
  have hspecEq :
      (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) =
        ∑ q ∈ S, modeMult q * c q ^ 2 := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hEigNonzero : cubeEig Q (natVec q) ≠ 0 := by
      have hpos := planar_cubeEig_lower_of_nonzero Q q (hS q hq)
      have hbase : 0 < 2 * Real.pi ^ 2 / cubeScaleFactor Q ^ 2 :=
        div_pos (by positivity) (sq_pos_of_pos (cubeScaleFactor_pos' Q))
      exact ne_of_gt (lt_of_lt_of_le hbase hpos)
    have hmult : modeMult q ≠ 0 := (modeMult_pos q).ne'
    dsimp [β, c]
    field_simp [hEigNonzero, hmult]
  have hFspec₀ := vectorPositiveHaarNorm_dirichletTestField_sq_le Q S β hS
  have hFspec : vectorPositiveHaarNorm Q F ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        (∑ q ∈ S, modeMult q * c q ^ 2) := by
    calc
      vectorPositiveHaarNorm Q F ^ 2 ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
          (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
            simpa [F] using hFspec₀
      _ = cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
          (∑ q ∈ S, modeMult q * c q ^ 2) := by rw [hspecEq]
  have hK : 0 ≤ vectorWeakHaarNorm Q G := Real.sqrt_nonneg _
  have hP : 0 ≤ vectorPositiveHaarNorm Q F := Real.sqrt_nonneg _
  have hA2 : (∑ q ∈ S, modeMult q * c q ^ 2) ^ 2 ≤
      vectorPositiveHaarNorm Q F ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by
    rw [← hpair]
    have hprod : 0 ≤ vectorPositiveHaarNorm Q F * vectorWeakHaarNorm Q G :=
      mul_nonneg hP hK
    calc
      vectorPairing Q G F ^ 2 = |vectorPairing Q G F| ^ 2 := by rw [sq_abs]
      _ ≤ (vectorPositiveHaarNorm Q F * vectorWeakHaarNorm Q G) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hdual 2
      _ = vectorPositiveHaarNorm Q F ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by ring
  have hA_bound : (∑ q ∈ S, modeMult q * c q ^ 2) ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        (∑ q ∈ S, modeMult q * c q ^ 2) * vectorWeakHaarNorm Q G ^ 2 := by
    calc
      _ ≤ vectorPositiveHaarNorm Q F ^ 2 * vectorWeakHaarNorm Q G ^ 2 := hA2
      _ ≤ (cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
          (∑ q ∈ S, modeMult q * c q ^ 2)) * vectorWeakHaarNorm Q G ^ 2 :=
            mul_le_mul_of_nonneg_right hFspec (sq_nonneg _)
  by_cases hA0 : ∑ q ∈ S, modeMult q * c q ^ 2 = 0
  · have hnonneg : 0 ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        vectorWeakHaarNorm Q G ^ 2 := by positivity
    simpa [c, hA0] using hnonneg
  · have hApos : 0 < ∑ q ∈ S, modeMult q * c q ^ 2 :=
      lt_of_le_of_ne hA (Ne.symm hA0)
    have hcancel : (∑ q ∈ S, modeMult q * c q ^ 2) ^ 2 ≤
        (cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
          vectorWeakHaarNorm Q G ^ 2) *
            (∑ q ∈ S, modeMult q * c q ^ 2) := by
      calc
        _ ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
              (∑ q ∈ S, modeMult q * c q ^ 2) * vectorWeakHaarNorm Q G ^ 2 := hA_bound
        _ = (cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
              vectorWeakHaarNorm Q G ^ 2) *
              (∑ q ∈ S, modeMult q * c q ^ 2) := by ring
    have hcancelMul :
        (∑ q ∈ S, modeMult q * c q ^ 2) *
            (∑ q ∈ S, modeMult q * c q ^ 2) ≤
          (cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
            vectorWeakHaarNorm Q G ^ 2) *
              (∑ q ∈ S, modeMult q * c q ^ 2) := by
      nlinarith [hcancel]
    have hfinal : ∑ q ∈ S, modeMult q * c q ^ 2 ≤
        cubeScaleFactor Q ^ 2 * planarCD ^ 2 * vectorWeakHaarNorm Q G ^ 2 :=
      le_of_mul_le_mul_right hcancelMul hApos
    calc
      ∑ q ∈ S, modeMult q *
          dirichletFourierCoeff Q u.toH1Function.toFun (natVec q) ^ 2 =
          ∑ q ∈ S, modeMult q * c q ^ 2 := by rfl
      _ ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
          vectorWeakHaarNorm Q G ^ 2 := hfinal

/-- Flipping one signed sine frequency changes the sign of the tensor mode. -/
theorem boxMode_update_neg (a : Fin 2 → ℝ) {ℓ : ℝ} (O : Finset (Fin 2))
    (p : Fin 2 → ℤ) (i : Fin 2) (x : Fin 2 → ℝ) :
    Torus.boxMode a ℓ O (Function.update p i (-p i)) x =
      (if i ∈ O then -1 else 1) * Torus.boxMode a ℓ O p x := by
  unfold Torus.boxMode
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have hfac : (if i ∈ O then
      Real.sin (Real.pi * Function.update p i (-p i) i * (x i - a i) / ℓ)
    else Real.cos (Real.pi * Function.update p i (-p i) i * (x i - a i) / ℓ)) =
      (if i ∈ O then -1 else 1) *
        (if i ∈ O then Real.sin (Real.pi * p i * (x i - a i) / ℓ)
          else Real.cos (Real.pi * p i * (x i - a i) / ℓ)) := by
    simp only [Function.update_self]
    split_ifs with hi
    · have harg : Real.pi * ↑(-p i) * (x i - a i) / ℓ =
          -(Real.pi * ↑(p i) * (x i - a i) / ℓ) := by push_cast; ring
      rw [harg, Real.sin_neg]
      ring
    · have harg : Real.pi * ↑(-p i) * (x i - a i) / ℓ =
          -(Real.pi * ↑(p i) * (x i - a i) / ℓ) := by push_cast; ring
      rw [harg, Real.cos_neg]
      ring
  have hrest : ∏ k ∈ Finset.univ.erase i, (if k ∈ O then
      Real.sin (Real.pi * Function.update p i (-p i) k * (x k - a k) / ℓ)
    else Real.cos (Real.pi * Function.update p i (-p i) k * (x k - a k) / ℓ)) =
      ∏ k ∈ Finset.univ.erase i, (if k ∈ O then
      Real.sin (Real.pi * p k * (x k - a k) / ℓ)
    else Real.cos (Real.pi * p k * (x k - a k) / ℓ)) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    rw [Function.update_of_ne hki]
  rw [hfac, hrest]
  split_ifs <;> ring

/-- A signed sine coefficient squared is even in each frequency coordinate. -/
theorem dirichletFourierCoeff_sq_update_neg (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (p : Fin 2 → ℤ) (i : Fin 2) :
    dirichletFourierCoeff Q f (Function.update p i (-p i)) ^ 2 =
      dirichletFourierCoeff Q f p ^ 2 := by
  unfold dirichletFourierCoeff
  have hfun : (fun x => Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q)
        Finset.univ (Function.update p i (-p i)) x * f x) =
      fun x => (if i ∈ Finset.univ then -1 else 1) *
        (Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p x * f x) := by
    funext x
    rw [boxMode_update_neg]
    simp
  rw [hfun, integral_const_mul]
  simp

private theorem dirichletFourierCoeff_sq_update_of_eq_or_neg (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (p : Fin 2 → ℤ) (i : Fin 2) (a : ℤ)
    (ha : a = p i ∨ a = -p i) :
    dirichletFourierCoeff Q f (Function.update p i a) ^ 2 =
      dirichletFourierCoeff Q f p ^ 2 := by
  rcases ha with ha | ha
  · subst a
    simp
  · rw [ha]
    exact dirichletFourierCoeff_sq_update_neg Q f p i

/-- Squared sine coefficients depend only on the componentwise absolute
frequency. -/
theorem dirichletFourierCoeff_sq_natAbsVec (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (p : Fin 2 → ℤ) :
    dirichletFourierCoeff Q f p ^ 2 =
      dirichletFourierCoeff Q f (natVec (natAbsVec p)) ^ 2 := by
  let q := natAbsVec p
  have hsign (i : Fin 2) :
      p i = (natVec q) i ∨ p i = -(natVec q) i := by
    simpa [q, natAbsVec, natVec] using (Int.natAbs_eq (p i))
  let r0 := Function.update (natVec q) 0 (p 0)
  let r1 := Function.update r0 1 (p 1)
  have hr : r1 = p := by
    ext i
    fin_cases i
    · simp [r1, r0]
    · simp [r1, r0]
  have h0 : dirichletFourierCoeff Q f r0 ^ 2 =
      dirichletFourierCoeff Q f (natVec q) ^ 2 :=
    dirichletFourierCoeff_sq_update_of_eq_or_neg Q f (natVec q) 0 (p 0) (hsign 0)
  have h1sign : p 1 = r0 1 ∨ p 1 = -r0 1 := by
    simpa [r0] using hsign 1
  have h1 : dirichletFourierCoeff Q f r1 ^ 2 =
      dirichletFourierCoeff Q f r0 ^ 2 :=
    dirichletFourierCoeff_sq_update_of_eq_or_neg Q f r0 1 (p 1) h1sign
  calc
    dirichletFourierCoeff Q f p ^ 2 = dirichletFourierCoeff Q f r1 ^ 2 := by rw [← hr]
    _ = dirichletFourierCoeff Q f (natVec q) ^ 2 := h1.trans h0

/-- A sine coefficient vanishes when any frequency coordinate is zero. -/
theorem dirichletFourierCoeff_eq_zero_of_coord_zero (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (p : Fin 2 → ℤ) (i : Fin 2) (hp : p i = 0) :
    dirichletFourierCoeff Q f p = 0 := by
  unfold dirichletFourierCoeff
  have hmode : ∀ x, Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q)
      Finset.univ p x = 0 := by
    intro x
    unfold Torus.boxMode
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    simp [hp]
  have hfun : (fun x => Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q)
      Finset.univ p x * f x) = fun _ => 0 := by
    funext x
    simp [hmode]
  rw [hfun, integral_zero]

/-- Away from the two reflection fixed points, the odd sign has unit modulus. -/
theorem oddSign_sq_eq_one_of_ne_zero (s : UnitAddCircle)
    (hs : Torus.oddSign s ≠ 0) : Torus.oddSign s ^ 2 = 1 := by
  unfold Torus.oddSign at hs ⊢
  by_cases h₁ : 0 < rep s ∧ rep s < 1 / 2
  · rw [ite_eq_left h₁]
    norm_num
  · by_cases h₂ : rep s < 0
    · rw [ite_eq_right h₁, ite_eq_left h₂]
      norm_num
    · rw [ite_eq_right h₁, ite_eq_right h₂] at hs
      norm_num at hs

/-- The zeros of the odd reflection sign are its two fixed points. -/
theorem oddSign_zero_rep_endpoint (s : UnitAddCircle)
    (hs : Torus.oddSign s = 0) : Torus.rep s = 0 ∨ Torus.rep s = 1 / 2 := by
  have hr := Torus.rep_mem s
  unfold Torus.oddSign at hs
  by_cases h₁ : 0 < Torus.rep s ∧ Torus.rep s < 1 / 2
  · rw [ite_eq_left h₁] at hs
    norm_num at hs
  · by_cases h₂ : Torus.rep s < 0
    · rw [ite_eq_right h₁, ite_eq_left h₂] at hs
      norm_num at hs
    · rw [ite_eq_right h₁, ite_eq_right h₂] at hs
      have hnonneg : 0 ≤ Torus.rep s := le_of_not_gt h₂
      by_cases hz : Torus.rep s = 0
      · exact Or.inl hz
      · have hpos : 0 < Torus.rep s := lt_of_le_of_ne hnonneg (Ne.symm hz)
        rcases hr.2.lt_or_eq with hlt | heq
        · exact False.elim (h₁ ⟨hpos, hlt⟩)
        · exact Or.inr heq

/-- A singleton has zero Haar measure on the circle, by pulling back to its
unique representative in the fundamental interval. -/
theorem volume_singleton_unitAddCircle (s : UnitAddCircle) :
    volume ({s} : Set UnitAddCircle) = 0 := by
  rw [← Torus.map_coe_restrict_Ioc]
  rw [Measure.map_apply AddCircle.measurable_mk' (measurableSet_singleton s)]
  rw [Measure.restrict_apply
    (AddCircle.measurable_mk' (measurableSet_singleton s))]
  apply measure_mono_null
  · intro x hx
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc,
      Set.mem_singleton_iff] at hx
    have hrep := congrArg Torus.rep hx.1
    rw [Torus.rep_coe hx.2] at hrep
    exact Set.mem_singleton_iff.mpr hrep
  · simp

/-- Parseval for the signed two-dimensional Dirichlet sine coefficients. The
odd-reflection signs have modulus one away from their null fixed-point set. -/
theorem hasSum_sq_dirichletFourierCoeff (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q))) :
    HasSum (fun p : Fin 2 → ℤ => dirichletFourierCoeff Q f p ^ 2)
      (∫ x, f x ^ 2 ∂Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
  have hbase := Torus.hasSum_sq_boxCoeff (cubeCorner Q)
    (cubeScaleFactor_pos' Q) Finset.univ hf
  have hnull : volume {s : UnitAddCircle | Torus.oddSign s = 0} = 0 := by
    have hsub : {s : UnitAddCircle | Torus.oddSign s = 0} ⊆
        {0} ∪ {((1 / 2 : ℝ) : UnitAddCircle)} := by
      intro s hs
      rcases oddSign_zero_rep_endpoint s hs with hzero | hhalf
      · left
        have hrep := Torus.coe_rep s
        rw [hzero] at hrep
        exact Set.mem_singleton_iff.mpr hrep.symm
      · right
        have hrep := Torus.coe_rep s
        rw [hhalf] at hrep
        exact Set.mem_singleton_iff.mpr hrep.symm
    have hunion : volume ({0} ∪ {((1 / 2 : ℝ) : UnitAddCircle)} :
        Set UnitAddCircle) = 0 := by
      refine le_antisymm ?_ bot_le
      exact (measure_union_le _ _).trans (by simp [volume_singleton_unitAddCircle])
    exact measure_mono_null hsub hunion
  have hodd : ∀ᵐ s : UnitAddCircle, Torus.oddSign s ≠ 0 := by
    rw [ae_iff]
    simpa using hnull
  have hsignsq : ∀ᵐ s : UnitAddCircle, Torus.oddSign s ^ 2 = 1 := by
    filter_upwards [hodd] with s hs
    exact oddSign_sq_eq_one_of_ne_zero s hs
  have hbad0 : volume {t : Fin 2 → UnitAddCircle |
      Torus.oddSign (t 0) ^ 2 ≠ 1} = 0 := by
    have heval : volume {t : Fin 2 → UnitAddCircle | Torus.oddSign (t 0) = 0} = 0 := by
      change (Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle)))
        {t : Fin 2 → UnitAddCircle | Torus.oddSign (t 0) = 0} = 0
      simpa using (Measure.pi_eval_preimage_null
        (fun _ : Fin 2 => (volume : Measure UnitAddCircle)) hnull :
          (Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle)))
            (Function.eval (0 : Fin 2) ⁻¹' {s : UnitAddCircle | Torus.oddSign s = 0}) = 0)
    refine measure_mono_null ?_ heval
    intro t ht
    by_contra hne
    exact ht (oddSign_sq_eq_one_of_ne_zero (t 0) hne)
  have hbad1 : volume {t : Fin 2 → UnitAddCircle |
      Torus.oddSign (t 1) ^ 2 ≠ 1} = 0 := by
    have heval : volume {t : Fin 2 → UnitAddCircle | Torus.oddSign (t 1) = 0} = 0 := by
      change (Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle)))
        {t : Fin 2 → UnitAddCircle | Torus.oddSign (t 1) = 0} = 0
      simpa using (Measure.pi_eval_preimage_null
        (fun _ : Fin 2 => (volume : Measure UnitAddCircle)) hnull :
          (Measure.pi (fun _ : Fin 2 => (volume : Measure UnitAddCircle)))
            (Function.eval (1 : Fin 2) ⁻¹' {s : UnitAddCircle | Torus.oddSign s = 0}) = 0)
    refine measure_mono_null ?_ heval
    intro t ht
    by_contra hne
    exact ht (oddSign_sq_eq_one_of_ne_zero (t 1) hne)
  have hfun : ∀ᵐ t : Fin 2 → UnitAddCircle,
      ((∏ i ∈ (Finset.univ : Finset (Fin 2)), Torus.oddSign (t i)) *
          f (Torus.boxMap (cubeCorner Q) (cubeScaleFactor Q) t)) ^ 2 =
        f (Torus.boxMap (cubeCorner Q) (cubeScaleFactor Q) t) ^ 2 := by
    rw [ae_iff]
    have hnullbad : volume ({t : Fin 2 → UnitAddCircle |
        Torus.oddSign (t 0) ^ 2 ≠ 1} ∪
          {t : Fin 2 → UnitAddCircle | Torus.oddSign (t 1) ^ 2 ≠ 1}) = 0 := by
      refine le_antisymm ?_ bot_le
      exact (measure_union_le _ _).trans (by rw [hbad0, hbad1]; simp)
    refine measure_mono_null ?_ hnullbad
    intro t ht
    by_contra hne
    have hzero0 : Torus.oddSign (t 0) ^ 2 = 1 := by
      by_contra hz
      exact hne (Or.inl hz)
    have hzero1 : Torus.oddSign (t 1) ^ 2 = 1 := by
      by_contra hz
      exact hne (Or.inr hz)
    have hprod : (∏ i : Fin 2, Torus.oddSign (t i)) ^ 2 = 1 := by
      rw [Fin.prod_univ_two, mul_pow, hzero0, hzero1]
      norm_num
    exact ht (by rw [mul_pow, hprod]; ring)
  have hmap : ∫ t, f (Torus.boxMap (cubeCorner Q) (cubeScaleFactor Q) t) ^ 2 =
      ∫ x, f x ^ 2 ∂Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q) :=
    Torus.integral_boxMap (cubeCorner Q) (cubeScaleFactor_pos' Q)
      (f := fun x => f x ^ 2) (hf.aestronglyMeasurable.pow 2)
  have htarget : (∫ t,
      ((∏ i ∈ (Finset.univ : Finset (Fin 2)), Torus.oddSign (t i)) *
        f (Torus.boxMap (cubeCorner Q) (cubeScaleFactor Q) t)) ^ 2) =
        ∫ x, f x ^ 2 ∂Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q) := by
    rw [integral_congr_ae hfun, hmap]
  have hcoeff : (fun p : Fin 2 → ℤ =>
      (∫ x, Torus.boxMode (cubeCorner Q) (cubeScaleFactor Q) Finset.univ p x * f x
        ∂Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) ^ 2) =
      fun p => dirichletFourierCoeff Q f p ^ 2 := by
    funext p
    rfl
  rw [← htarget]
  exact hbase.congr_fun (fun p => (congrFun hcoeff p).symm)

/-- Every finite signed-frequency sine coefficient sum is bounded by the
spectral Poisson estimate on its positive absolute-frequency classes. -/
theorem finite_signed_dirichlet_sum_le (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (T : Finset (Fin 2 → ℤ)) :
    ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) ^ 2 := by
  let c : (Fin 2 → ℕ) → ℝ := fun q =>
    dirichletFourierCoeff Q u.toH1Function.toFun (natVec q)
  let A := T.image natAbsVec
  let S := A.filter fun q => ∀ i, q i ≠ 0
  have hgroup : ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2 ≤
      ∑ q ∈ A, modeMult q * c q ^ 2 := by
    calc
      ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2 =
          ∑ p ∈ T,
            dirichletFourierCoeff Q u.toH1Function.toFun
              (natVec (natAbsVec p)) ^ 2 := by
                apply Finset.sum_congr rfl
                intro p hp
                exact dirichletFourierCoeff_sq_natAbsVec Q u.toH1Function.toFun p
      _ ≤ ∑ q ∈ A, modeMult q * c q ^ 2 := by
            exact sum_le_sum_image_natAbsVec T (fun q => c q ^ 2)
              (fun q => sq_nonneg (c q))
  have hremove : ∑ q ∈ A, modeMult q * c q ^ 2 =
      ∑ q ∈ S, modeMult q * c q ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hnot
    have hcoords : ¬ ∀ i, q i ≠ 0 := by
      intro hpos
      exact hnot (Finset.mem_filter.mpr ⟨hq, hpos⟩)
    obtain ⟨i, hi⟩ := not_forall.mp hcoords
    have hi' : q i = 0 := by omega
    have hzero : (natVec q) i = 0 := by simp [natVec, hi']
    have hc : c q = 0 := by
      exact dirichletFourierCoeff_eq_zero_of_coord_zero Q
        u.toH1Function.toFun (natVec q) i hzero
    simp [c, hc]
  have hS : ∀ q ∈ S, ∀ i, q i ≠ 0 := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hfinite := finite_dirichlet_weakHaar_bound Q u S hS
  calc
    ∑ p ∈ T, dirichletFourierCoeff Q u.toH1Function.toFun p ^ 2
        ≤ ∑ q ∈ A, modeMult q * c q ^ 2 := hgroup
    _ = ∑ q ∈ S, modeMult q * c q ^ 2 := hremove
    _ ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) ^ 2 := by
          simpa [c] using hfinite

/-- The sharp `L²` Dirichlet bridge for zero-trace `H¹` data. -/
theorem dirichlet_L2_bridge_sq (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    energy Q u.toH1Function.toFun ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) ^ 2 := by
  have huNorm : MemLp u.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On u.toH1Function.memL2
  have huBox : MemLp u.toH1Function.toFun 2
      (Torus.boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
    rw [boxMeasure_eq_normalizedCubeMeasure Q]
    exact huNorm
  have hparseval := hasSum_sq_dirichletFourierCoeff Q huBox
  rw [boxMeasure_eq_normalizedCubeMeasure Q] at hparseval
  rw [energy_eq_integral_sq Q, ← hparseval.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun p => sq_nonneg
      (dirichletFourierCoeff Q u.toH1Function.toFun p)) ?_
  intro T
  exact finite_signed_dirichlet_sum_le Q u T

/-- The sharp `L²` Dirichlet bridge in norm form. -/
theorem dirichlet_L2_bridge (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    Real.sqrt (energy Q u.toH1Function.toFun) ≤
      cubeScaleFactor Q * planarCD *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  have hsq := dirichlet_L2_bridge_sq Q u
  have hnonneg : 0 ≤ cubeScaleFactor Q * planarCD *
      vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) :=
    mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_iff]
  refine ⟨hnonneg, ?_⟩
  nlinarith [hsq]

end ASDExplicitGamma.Triadic

end
