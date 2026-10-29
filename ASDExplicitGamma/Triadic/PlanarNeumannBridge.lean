module

public import ASDExplicitGamma.Triadic.PlanarDirichletSpectral
public import ASDExplicitGamma.Triadic.NeumannBlock
public import ASDExplicitGamma.Triadic.NeumannTest
public import ASDExplicitGamma.Triadic.NeumannSpectral
public import ASDExplicitGamma.Triadic.PlanarDirichletBridge
public import Homogenization.Sobolev.H1.Algebra.H1Function
public import Homogenization.Multiscale.NormalizedNorms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact Neumann cosine estimates used by the positive-Haar Dirichlet bridge. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Triadic

open Torus

/-- Smoothness of a finite cosine Neumann test field. -/
theorem contDiff_neumannTestField (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ) (j : Fin 2)
    {m : ℕ∞} : ContDiff ℝ m (testField Q S β j) := by
  unfold testField
  refine ContDiff.sum fun q hq => ?_
  exact contDiff_const.mul
    (contDiff_cubeDirichletMode Q {j} (natVec q) (m := m))

/-- A finite cosine Neumann test field as an `H¹` function. -/
noncomputable def neumannTestFieldH1 (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ) (j : Fin 2) :
    H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_neumannTestField Q S β j (m := 1))

@[simp] theorem neumannTestFieldH1_toFun (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ) (j : Fin 2) :
    (neumannTestFieldH1 Q S β j).toFun = testField Q S β j := rfl

/-- The finite Neumann test field has the Hessian displayed in `NeumannTest`. -/
theorem fderiv_neumannTestField_apply (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ)
    (j i : Fin 2) (x : Vec 2) :
    (fderiv ℝ (testField Q S β j) x) (basisVec i) = testHess Q S β j i x := by
  have hf : DifferentiableAt ℝ (testField Q S β j) x :=
    ((contDiff_neumannTestField Q S β j (m := 1)).differentiable (by simp)) x
  have hline : HasDerivAt (fun t => Function.update x i t) (basisVec i) (x i) := by
    convert (hasFDerivAt_update x (x i)).hasDerivAt using 1
    ext k
    by_cases hki : k = i <;> simp [basisVec, hki]
  have hf' : DifferentiableAt ℝ (testField Q S β j)
      (Function.update x i (x i)) := by simpa using hf
  have hchain := fderiv_comp_deriv (l := testField Q S β j)
    (f := fun t => Function.update x i t) (x := x i) hf' hline.differentiableAt
  have hchain' := hchain
  rw [hline.deriv, Function.update_eq_self] at hchain'
  change deriv (fun t => testField Q S β j (Function.update x i t)) (x i) = _ at hchain'
  rw [(hasDerivAt_testField Q S β j i x).deriv] at hchain'
  exact hchain'.symm

theorem neumannTestFieldH1_grad (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ)
    (j i : Fin 2) (x : Vec 2) :
    (neumannTestFieldH1 Q S β j).grad x i = testHess Q S β j i x := by
  exact fderiv_neumannTestField_apply Q S β j i x

/-- The exact component energies of a finite Neumann test field. -/
theorem energy_neumannTestField (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ) (j : Fin 2) :
    energy Q (testField Q S β j) =
      ∑ q ∈ S, β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 / modeMult q := by
  rw [energy_eq_integral_sq, ← boxMeasure_eq_normalizedCubeMeasure]
  unfold testField
  rw [integral_sq_sum_boxMode _ (cubeScaleFactor_pos' Q)]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hzero : ∀ k ∈ ({j} : Finset (Fin 2)), q k = 0 →
      β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 = 0 := by
    intro k hk hqk
    have hkj : k = j := Finset.mem_singleton.mp hk
    subst k
    rw [cubeFreq_natVec_eq_zero Q hqk]
    ring
  rw [show (-(β q) * cubeFreq Q (natVec q) j) ^ 2 =
      β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 by ring]
  exact mul_boxNormSq_eq_div {j} q hzero

theorem sum_energy_neumannTestField (Q : TriadicCube 2)
    (S : Finset (Fin 2 → ℕ)) (β : (Fin 2 → ℕ) → ℝ) :
    ∑ j : Fin 2, energy Q (testField Q S β j) =
      ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q := by
  simp_rw [energy_neumannTestField]
  calc
    ∑ j : Fin 2, ∑ q ∈ S,
        β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 / modeMult q
        = ∑ q ∈ S, ∑ j : Fin 2,
          β q ^ 2 * cubeFreq Q (natVec q) j ^ 2 / modeMult q := by
            rw [Finset.sum_comm]
    _ = ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      unfold cubeEig
      ring

/-- The exact `L²` to Laplacian-energy bound for finite Neumann gradients. -/
theorem vectorPositiveHaarNorm_neumannTestField_sq_le
    (Q : TriadicCube 2) (S : Finset (Fin 2 → ℕ))
    (β : (Fin 2 → ℕ) → ℝ) (hS : ∀ q ∈ S, q ≠ 0) :
    vectorPositiveHaarNorm Q (fun x j => testField Q S β j x) ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
        (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
  have hpos : ∀ j : Fin 2,
      positiveHaarNorm Q (testField Q S β j) ^ 2 ≤
        energy Q (testField Q S β j) +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            ∑ i : Fin 2, energy Q (testHess Q S β j i) := by
    intro j
    have hu := neumannTestFieldH1 Q S β j
    have hf : MemLp (testField Q S β j) 2 (normalizedCubeMeasure Q) := by
      simpa only [neumannTestFieldH1_toFun] using
        (neumannTestFieldH1 Q S β j).memL2_normalizedCubeMeasure
    have hG : ∀ i : Fin 2,
        MemLp (fun x => testHess Q S β j i x) 2 (normalizedCubeMeasure Q) := by
      intro i
      simpa only [neumannTestFieldH1_grad] using
        (neumannTestFieldH1 Q S β j).grad_memL2_normalizedCubeMeasure i
    have hw : HasWeakGradientOn (openCubeSet Q) (testField Q S β j)
        (fun x i => testHess Q S β j i x) := by
      have h := (neumannTestFieldH1 Q S β j).hasWeakGradient
      have hgrad : (neumannTestFieldH1 Q S β j).grad =
          fun x i => testHess Q S β j i x := by
        funext x i
        exact neumannTestFieldH1_grad Q S β j i x
      have hfun : (neumannTestFieldH1 Q S β j).toFun =
          testField Q S β j := neumannTestFieldH1_toFun Q S β j
      rw [hfun, hgrad] at h
      exact h
    exact positiveHaarNorm_sq_le_l2_add_gradient Q hf hG hw
  rw [vectorPositiveHaarNorm_sq]
  calc
    ∑ j : Fin 2, positiveHaarNorm Q (testField Q S β j) ^ 2 ≤
        ∑ j : Fin 2, (energy Q (testField Q S β j) +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            ∑ i : Fin 2, energy Q (testHess Q S β j i)) :=
          Finset.sum_le_sum fun j _ => hpos j
    _ = (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q) +
          cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
            (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_energy_neumannTestField,
          sum_energy_testHess]
    _ ≤ cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
          (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
        have hEigLower : ∀ q ∈ S,
            Real.pi ^ 2 / cubeScaleFactor Q ^ 2 ≤ cubeEig Q (natVec q) := by
          intro q hq
          obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
            by_contra hn
            push Not at hn
            exact hS q hq (funext hn)
          have hqi : (1 : ℝ) ≤ q i := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
          have hfreq : Real.pi / cubeScaleFactor Q ≤ cubeFreq Q (natVec q) i := by
            unfold cubeFreq natVec
            push_cast
            apply (div_le_div_of_nonneg_right ?_ (cubeScaleFactor_pos' Q).le)
            simpa using mul_le_mul_of_nonneg_left hqi Real.pi_pos.le
          have hfreqsq : (Real.pi / cubeScaleFactor Q) ^ 2 ≤
              cubeFreq Q (natVec q) i ^ 2 := by
            apply (sq_le_sq₀
              (div_nonneg Real.pi_pos.le (cubeScaleFactor_pos' Q).le)
              (le_trans (div_nonneg Real.pi_pos.le (cubeScaleFactor_pos' Q).le)
                hfreq)).2
            exact hfreq
          have hsingle : cubeFreq Q (natVec q) i ^ 2 ≤ cubeEig Q (natVec q) := by
            unfold cubeEig
            exact Finset.single_le_sum (fun k _ => sq_nonneg (cubeFreq Q (natVec q) k))
              (Finset.mem_univ i)
          have hratio : (Real.pi / cubeScaleFactor Q) ^ 2 =
              Real.pi ^ 2 / cubeScaleFactor Q ^ 2 := by rw [div_pow]
          rw [← hratio]
          exact hfreqsq.trans hsingle
        have hterms : ∀ q ∈ S,
            β q ^ 2 * cubeEig Q (natVec q) / modeMult q ≤
              cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
                (β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
          intro q hq
          have hEig := hEigLower q hq
          have hbase : 0 < Real.pi ^ 2 / cubeScaleFactor Q ^ 2 :=
            div_pos (sq_pos_of_pos Real.pi_pos)
              (sq_pos_of_pos (cubeScaleFactor_pos' Q))
          have hEigPos : 0 < cubeEig Q (natVec q) := lt_of_lt_of_le hbase hEig
          have hfactor : 1 ≤ cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
              cubeEig Q (natVec q) := by
            calc
              1 = cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
                    (Real.pi ^ 2 / cubeScaleFactor Q ^ 2) := by
                      field_simp [Real.pi_ne_zero,
                        ne_of_gt (cubeScaleFactor_pos' Q)]
              _ ≤ cubeScaleFactor Q ^ 2 / Real.pi ^ 2 * cubeEig Q (natVec q) :=
                    mul_le_mul_of_nonneg_left hEig
                      (div_nonneg (sq_nonneg _) (sq_nonneg _))
          have hcoef : 0 ≤ β q ^ 2 * cubeEig Q (natVec q) / modeMult q :=
            div_nonneg (mul_nonneg (sq_nonneg _) hEigPos.le) (modeMult_pos q).le
          calc
            β q ^ 2 * cubeEig Q (natVec q) / modeMult q =
                (β q ^ 2 * cubeEig Q (natVec q) / modeMult q) * 1 := by ring
            _ ≤ (β q ^ 2 * cubeEig Q (natVec q) / modeMult q) *
                (cubeScaleFactor Q ^ 2 / Real.pi ^ 2 * cubeEig Q (natVec q)) :=
                  mul_le_mul_of_nonneg_left hfactor hcoef
            _ = cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
                (β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by ring
        have hsum :
            (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q) ≤
              cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
                (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
          calc
            _ ≤ ∑ q ∈ S, cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
                (β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) :=
                  Finset.sum_le_sum fun q hq => hterms q hq
            _ = _ := by rw [Finset.mul_sum]
        have hcoeff : planarC0 ^ 2 = planarC1 ^ 2 + 1 / Real.pi ^ 2 :=
          planarC0_sq_eq_planarC1_sq_add
        have hA : 0 ≤ ∑ q ∈ S,
            β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q :=
          Finset.sum_nonneg fun q _ => div_nonneg
            (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (modeMult_pos q).le
        have hR : 0 ≤ cubeScaleFactor Q ^ 2 := sq_nonneg _
        calc
          (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) / modeMult q) +
              cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
                (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q)
              ≤ cubeScaleFactor Q ^ 2 / Real.pi ^ 2 *
                  (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) +
                cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
                  (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
                    exact add_le_add hsum (le_refl _)
          _ = cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
                (∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q) := by
                  rw [hcoeff]
                  ring

/-- Finite cosine coefficients of a mean-zero Neumann primitive are bounded
by the weak Haar size of its vector source. -/
theorem neumann_finite_coeff_bound (Q : TriadicCube 2)
    {G : Vec 2 → Vec 2} (hG : ∀ j,
      MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    {w : H1Function (openCubeSet Q)}
    (hw : ASDExplicitGamma.Triadic.Support.Localization.IsNeumannPrimitive Q G w)
    (S : Finset (Fin 2 → ℕ)) (hS : ∀ q ∈ S, q ≠ 0) :
    ∑ q ∈ S, modeMult q *
        (∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by
  classical
  let coeff : (Fin 2 → ℕ) → ℝ := fun q =>
    ∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q
  let β : (Fin 2 → ℕ) → ℝ := fun q =>
    modeMult q * coeff q / cubeEig Q (natVec q)
  let V : Vec 2 → Vec 2 := fun x j => testField Q S β j x
  let A : ℝ := ∑ q ∈ S, modeMult q * coeff q ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (modeMult_pos q).le (sq_nonneg _)
  have hEig : ∀ q ∈ S, cubeEig Q (natVec q) ≠ 0 := by
    intro q hq
    exact (cubeEig_natVec_pos Q (hS q hq)).ne'
  have hDual : A = vectorPairing Q V G := by
    calc
      (∑ q ∈ S, modeMult q * coeff q ^ 2) =
          ∑ j : Fin 2, pairing Q (fun x => G x j) (testField Q S β j) := by
            rw [Finset.sum_congr rfl fun j _ => pairing_testField Q S β j (hG j),
              Finset.sum_comm]
            refine Finset.sum_congr rfl fun q hq => ?_
            have hid := neumann_coeff_identity Q hG hw (natVec q)
            have h1 : ∑ j : Fin 2,
                (-(β q) * cubeFreq Q (natVec q) j) *
                  ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q =
                -(β q) * ∑ j : Fin 2, cubeFreq Q (natVec q) j *
                  ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
            rw [h1, ← neg_neg (∑ j : Fin 2, cubeFreq Q (natVec q) j *
              ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q), ← hid]
            dsimp [β, coeff]
            field_simp [hEig q hq]
      _ = vectorPairing Q V G := by
            unfold vectorPairing
            dsimp [V]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [pairing_comm]
  have hF : ∀ j, MemLp (fun x => V x j) 2 (normalizedCubeMeasure Q) := by
    intro j
    change MemLp (testField Q S β j) 2 (normalizedCubeMeasure Q)
    exact memLp_testField Q S β j
  have hFpos : ∀ j, Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => V x j))) := by
    intro j
    change Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (testField Q S β j)))
    have hf : MemLp (testField Q S β j) 2 (normalizedCubeMeasure Q) := by
      simpa only [neumannTestFieldH1_toFun] using
        (neumannTestFieldH1 Q S β j).memL2_normalizedCubeMeasure
    have hGi : ∀ i : Fin 2,
        MemLp (fun x => testHess Q S β j i x) 2 (normalizedCubeMeasure Q) := by
      intro i
      simpa only [neumannTestFieldH1_grad] using
        (neumannTestFieldH1 Q S β j).grad_memL2_normalizedCubeMeasure i
    have hwv : HasWeakGradientOn (openCubeSet Q) (testField Q S β j)
        (fun x i => testHess Q S β j i x) := by
      have h := (neumannTestFieldH1 Q S β j).hasWeakGradient
      have hgrad : (neumannTestFieldH1 Q S β j).grad =
          fun x i => testHess Q S β j i x := by
        funext x i
        exact neumannTestFieldH1_grad Q S β j i x
      have hfun : (neumannTestFieldH1 Q S β j).toFun =
          testField Q S β j := neumannTestFieldH1_toFun Q S β j
      rw [hfun, hgrad] at h
      exact h
    exact positiveHaarIncrementSeries_summable Q hf hGi hwv
  have hPair :=
    abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
      Q hF hG hFpos
  have hFinite := vectorPositiveHaarNorm_neumannTestField_sq_le Q S β hS
  have hHess :
      ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q = A := by
    dsimp [A, coeff, β]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hm := (modeMult_pos q).ne'
    field_simp [hEig q hq, hm]
  have hFinite' : vectorPositiveHaarNorm Q V ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * A := by
    rw [← hHess]
    simpa only [V] using hFinite
  have hVbound : vectorPositiveHaarNorm Q V ≤
      cubeScaleFactor Q * planarC0 * Real.sqrt A := by
    have hC : 0 ≤ cubeScaleFactor Q * planarC0 :=
      mul_nonneg (cubeScaleFactor_pos' Q).le (by unfold planarC0; positivity)
    have hSq : (cubeScaleFactor Q * planarC0 * Real.sqrt A) ^ 2 =
        cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * A := by
      rw [mul_pow, Real.sq_sqrt hA]
      ring
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mp
    rw [hSq]
    exact hFinite'
  have hAupper : A ≤ vectorPositiveHaarNorm Q V * vectorWeakHaarNorm Q G := by
    calc
      A ≤ |vectorPairing Q V G| := by rw [hDual]; exact le_abs_self _
      _ ≤ vectorPositiveHaarNorm Q V * vectorWeakHaarNorm Q G := hPair
  have hnonnegV : 0 ≤ vectorPositiveHaarNorm Q V := Real.sqrt_nonneg _
  have hnonnegK : 0 ≤ vectorWeakHaarNorm Q G := Real.sqrt_nonneg _
  have hcross : A ≤ cubeScaleFactor Q * planarC0 * Real.sqrt A *
      vectorWeakHaarNorm Q G := hAupper.trans (mul_le_mul_of_nonneg_right hVbound hnonnegK)
  change A ≤ cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * vectorWeakHaarNorm Q G ^ 2
  by_cases hAzero : A = 0
  · rw [hAzero]
    positivity
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have hsqrt : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
    have hrootBound : Real.sqrt A ≤ cubeScaleFactor Q * planarC0 *
        vectorWeakHaarNorm Q G := by
      have hcross' : Real.sqrt A ^ 2 ≤
          (cubeScaleFactor Q * planarC0 * vectorWeakHaarNorm Q G) * Real.sqrt A := by
        calc
          Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
          _ ≤ cubeScaleFactor Q * planarC0 * Real.sqrt A *
              vectorWeakHaarNorm Q G := hcross
          _ = (cubeScaleFactor Q * planarC0 * vectorWeakHaarNorm Q G) *
              Real.sqrt A := by ring
      have hmul : Real.sqrt A * Real.sqrt A ≤
          (cubeScaleFactor Q * planarC0 * vectorWeakHaarNorm Q G) * Real.sqrt A := by
        simpa only [pow_two] using hcross'
      exact le_of_mul_le_mul_right hmul hsqrt
    have hrootSq := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg
      (mul_nonneg (cubeScaleFactor_pos' Q).le (by unfold planarC0; positivity)) hnonnegK)).2 hrootBound
    calc
      A = Real.sqrt A ^ 2 := (Real.sq_sqrt hA).symm
      _ ≤ (cubeScaleFactor Q * planarC0 * vectorWeakHaarNorm Q G) ^ 2 := hrootSq
      _ = cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by ring

/-- Parseval upgrades the finite Neumann coefficient bounds to the full
mean-zero `L²` bridge. -/
theorem neumann_L2_bridge_sq (Q : TriadicCube 2)
    {G : Vec 2 → Vec 2} (hG : ∀ j,
      MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    {w : H1Function (openCubeSet Q)}
    (hw : ASDExplicitGamma.Triadic.Support.Localization.IsNeumannPrimitive Q G w) :
    energy Q w.toFun ≤ cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
      vectorWeakHaarNorm Q G ^ 2 := by
  classical
  let coeff : (Fin 2 → ℕ) → ℝ := fun q =>
    ∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q
  have hwL : MemLp w.toFun 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On w.memL2
  have hParseval : HasSum
      (fun p : Fin 2 → ℤ =>
        (∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2)
      (∫ x, w.toFun x ^ 2 ∂normalizedCubeMeasure Q) := by
    have huB : MemLp w.toFun 2 (boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
      rw [boxMeasure_eq_normalizedCubeMeasure]
      exact hwL
    have h := hasSum_sq_boxCoeff_cos (cubeCorner Q) (cubeScaleFactor_pos' Q) huB
    rw [boxMeasure_eq_normalizedCubeMeasure] at h
    exact h
  have hzero : coeff 0 = 0 := by
    dsimp [coeff]
    simp only [cubeCos_natVec_zero, one_mul]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    exact hw.1
  rw [energy_eq_integral_sq, ← hParseval.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun p => sq_nonneg _) fun T => ?_
  calc
    ∑ p ∈ T,
        (∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2
        = ∑ p ∈ T, coeff (natAbsVec p) ^ 2 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [cubeCos_natAbsVec Q p]
    _ ≤ ∑ q ∈ T.image natAbsVec, modeMult q * coeff q ^ 2 :=
          sum_le_sum_image_natAbsVec T (fun q => coeff q ^ 2) (fun q => sq_nonneg _)
    _ = ∑ q ∈ (T.image natAbsVec).erase 0, modeMult q * coeff q ^ 2 := by
          exact (Finset.sum_erase _ (by simp [hzero])).symm
    _ ≤ cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * vectorWeakHaarNorm Q G ^ 2 := by
          simpa only [coeff] using
            neumann_finite_coeff_bound Q hG hw ((T.image natAbsVec).erase 0)
              (fun q hq => Finset.ne_of_mem_erase hq)

/-- The constant function, bundled as an H¹ function on a triadic cube. -/
noncomputable def h1ConstantOnCube (Q : TriadicCube 2) (c : ℝ) :
    H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (f := fun _ : Vec 2 => c) contDiff_const

@[simp] theorem h1ConstantOnCube_toFun (Q : TriadicCube 2) (c : ℝ) :
    (h1ConstantOnCube Q c).toFun = fun _ => c := rfl

@[simp] theorem h1ConstantOnCube_grad (Q : TriadicCube 2) (c : ℝ) :
    (h1ConstantOnCube Q c).grad = 0 := by
  funext x i
  change (fderiv ℝ (fun _ : Vec 2 => c) x) (basisVec i) = 0
  simp

/-- A mean-zero fluctuation of an H¹ function is its Neumann primitive for
its own weak gradient. -/
theorem h1_fluctuation_isNeumannPrimitive (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    ASDExplicitGamma.Triadic.Support.Localization.IsNeumannPrimitive Q
      u.grad
      (u - h1ConstantOnCube Q (cubeAverage Q u.toFun)) := by
  constructor
  · rw [H1Function.sub_toFun, h1ConstantOnCube_toFun,
      cubeAverage_sub_const_of_memLp_two Q u.memL2_normalizedCubeMeasure]
    simp
  · intro φ
    have hgrad : (u - h1ConstantOnCube Q (cubeAverage Q u.toFun)).grad = u.grad := by
      rw [H1Function.sub_grad, h1ConstantOnCube_grad]
      funext x i
      simp
    rw [hgrad]

/-- Sharp local mean-zero L² control by the weak Haar norm of the gradient. -/
theorem h1_fluctuation_L2_bridge_sq (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    energy Q (fun x => u.toFun x - cubeAverage Q u.toFun) ≤
      cubeScaleFactor Q ^ 2 * planarC0 ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.grad x i) ^ 2 := by
  have hG : ∀ i, MemLp (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) :=
    u.grad_memL2_normalizedCubeMeasure
  have hbridge := neumann_L2_bridge_sq Q hG (h1_fluctuation_isNeumannPrimitive Q u)
  simpa [H1Function.sub_toFun, h1ConstantOnCube_toFun] using hbridge

/-- A local projection inside a descendant agrees with the corresponding
global projection on that descendant. -/
theorem energy_localProjection_eq (Q U : TriadicCube 2) (j k : ℕ)
    (f : Vec 2 → ℝ) (hU : U ∈ descendantsAtDepth Q j) :
    energy U (cubeProjection U k f) = energy U (cubeProjection Q (j + k) f) := by
  have hpoint : ∀ x ∈ cubeSet U,
      cubeProjection U k f x = cubeProjection Q (j + k) f x := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    have hTQ : T ∈ descendantsAtDepth Q (j + k) := mem_descendantsAtDepth_add hU hT
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hT hxT,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hTQ hxT]
  unfold energy pairing
  apply cubeAverage_congr_on_cubeSet
  intro x hx
  rw [hpoint x hx]

/-- Averaging local projection energies over the descendants gives the
corresponding global projection energy. -/
theorem descendantsAverage_localProjection_eq (Q : TriadicCube 2)
    (j k : ℕ) (f : Vec 2 → ℝ) :
    descendantsAverage Q j (fun U => energy U (cubeProjection U k f)) =
      energy Q (cubeProjection Q (j + k) f) := by
  rw [energy_eq_descendantsAverage Q j
    (projection_memLp Q (j + k) f 2)]
  unfold descendantsAverage
  change (↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ U ∈ descendantsAtDepth Q j, energy U (cubeProjection U k f) =
    (↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
      ∑ U ∈ descendantsAtDepth Q j, energy U (cubeProjection Q (j + k) f)
  apply congrArg (fun x : ℝ => (↑(descendantsAtDepth Q j).card : ℝ)⁻¹ * x)
  refine Finset.sum_congr rfl fun U hU => ?_
  exact energy_localProjection_eq Q U j k f hU

/-- The average local weak Haar energy is the global weak Haar energy with its
first `j` projection levels removed. -/
theorem descendantsAverage_dualEnergy_le (Q : TriadicCube 2) (j : ℕ)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun U => dualEnergy U (Real.sqrt 3) f) ≤
      (Real.sqrt 3) ^ j * dualEnergy Q (Real.sqrt 3) f := by
  let D := descendantsAtDepth Q j
  let q : ℝ := Real.sqrt 3
  let r : ℝ := q⁻¹
  let localTerm : TriadicCube 2 → ℕ → ℝ := fun U k =>
    r ^ k * energy U (cubeProjection U k f)
  have hq1 : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hr : 0 ≤ r := inv_nonneg.mpr hq0.le
  have hfactor : 0 ≤ 1 - r := by
    have hrlt : r < 1 := (inv_lt_one₀ hq0).2 hq1
    dsimp [r]
    linarith
  have hLocalLp : ∀ U ∈ D,
      MemLp f 2 (normalizedCubeMeasure U) := by
    intro U hU
    exact memLp_on_descendant_of_memLp hU hf
  have hlocalSummable : ∀ U ∈ D, Summable (localTerm U) := by
    intro U hU
    dsimp [localTerm, r, q]
    exact summable_weighted_projections U hq1 (hLocalLp U hU)
  have hswap : (∑' k : ℕ, ∑ U ∈ D, localTerm U k) =
      ∑ U ∈ D, ∑' k : ℕ, localTerm U k :=
    Summable.tsum_finsetSum hlocalSummable
  have hAvgProjection : ∀ k : ℕ,
      (D.card : ℝ)⁻¹ * ∑ U ∈ D,
          energy U (cubeProjection U k f) =
        energy Q (cubeProjection Q (j + k) f) := by
    intro k
    change descendantsAverage Q j
        (fun U => energy U (cubeProjection U k f)) = _
    exact descendantsAverage_localProjection_eq Q j k f
  have hExpansion : descendantsAverage Q j
      (fun U => dualEnergy U q f) =
      (1 - r) * ∑' k : ℕ, r ^ k *
        energy Q (cubeProjection Q (j + k) f) := by
    unfold descendantsAverage
    dsimp [D]
    rw [Finset.sum_congr rfl fun U hU =>
      dualEnergy_eq U hq1 (hLocalLp U hU)]
    calc
      (↑(descendantsAtDepth Q j).card)⁻¹ *
          ∑ U ∈ descendantsAtDepth Q j,
            ((1 - q⁻¹) * ∑' k : ℕ, q⁻¹ ^ k *
              energy U (cubeProjection U k f))
          = (1 - r) * ((↑(descendantsAtDepth Q j).card)⁻¹ *
              ∑ U ∈ descendantsAtDepth Q j, ∑' k : ℕ, localTerm U k) := by
                simp only [localTerm, r, q]
                rw [← Finset.mul_sum]
                ring
      _ = (1 - r) * ((↑(descendantsAtDepth Q j).card)⁻¹ *
            ∑' k : ℕ, ∑ U ∈ descendantsAtDepth Q j, localTerm U k) := by
              rw [← hswap]
      _ = (1 - r) * ∑' k : ℕ, r ^ k *
            energy Q (cubeProjection Q (j + k) f) := by
              rw [← tsum_mul_left]
              apply congrArg (fun t : ℝ => (1 - r) * t)
              apply tsum_congr
              intro k
              calc
                (↑(descendantsAtDepth Q j).card)⁻¹ *
                    ∑ U ∈ descendantsAtDepth Q j, localTerm U k =
                  r ^ k * ((↑(descendantsAtDepth Q j).card)⁻¹ *
                    ∑ U ∈ descendantsAtDepth Q j,
                      energy U (cubeProjection U k f)) := by
                        dsimp [localTerm]
                        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                        refine Finset.sum_congr rfl fun U hU => ?_
                        ring
                _ = r ^ k * energy Q (cubeProjection Q (j + k) f) := by
                      rw [hAvgProjection k]
  have ha : Summable (fun n : ℕ => r ^ n *
      energy Q (cubeProjection Q n f)) :=
    summable_weighted_projections Q hq1 hf
  have htail := ha.sum_add_tsum_nat_add j
  have hprefix : 0 ≤ ∑ n ∈ Finset.range j,
      r ^ n * energy Q (cubeProjection Q n f) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hr _) (energy_nonneg Q _)
  have htaille : (∑' k : ℕ, r ^ (k + j) *
      energy Q (cubeProjection Q (k + j) f)) ≤
      ∑' n : ℕ, r ^ n * energy Q (cubeProjection Q n f) := by
    linarith
  have hshift : ∑' k : ℕ, r ^ k *
      energy Q (cubeProjection Q (j + k) f) = q ^ j *
      (∑' k : ℕ, r ^ (k + j) *
        energy Q (cubeProjection Q (k + j) f)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have hcancel : q ^ j * r ^ j = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hq0), one_pow]
    rw [Nat.add_comm k j]
    calc
      r ^ k * energy Q (cubeProjection Q (j + k) f) =
          1 * (r ^ k * energy Q (cubeProjection Q (j + k) f)) := by ring
      _ = (q ^ j * r ^ j) *
          (r ^ k * energy Q (cubeProjection Q (j + k) f)) := by rw [hcancel]
      _ = q ^ j * (r ^ (j + k) *
          energy Q (cubeProjection Q (j + k) f)) := by rw [pow_add]; ring
  have hglobal := dualEnergy_eq Q hq1 hf
  calc
    descendantsAverage Q j (fun U => dualEnergy U q f) =
        (1 - r) * ∑' k : ℕ, r ^ k *
          energy Q (cubeProjection Q (j + k) f) := hExpansion
    _ = q ^ j * ((1 - r) *
          ∑' k : ℕ, r ^ (k + j) * energy Q (cubeProjection Q (k + j) f)) := by
            rw [hshift]
            ring
    _ ≤ q ^ j * ((1 - r) *
          ∑' n : ℕ, r ^ n * energy Q (cubeProjection Q n f)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0.le _)
            exact mul_le_mul_of_nonneg_left htaille hfactor
    _ = q ^ j * dualEnergy Q q f := by
          rw [← hglobal]

/-- Descendant weak Haar energies aggregate with the exact geometric scale. -/
theorem descendantsAverage_vectorWeakEnergy_le (Q : TriadicCube 2) (j : ℕ)
    {G : Vec 2 → Vec 2}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    descendantsAverage Q j (fun U =>
      vectorWeakHaarEnergy U (fun x i => G x i)) ≤
      (Real.sqrt 3) ^ j * vectorWeakHaarEnergy Q (fun x i => G x i) := by
  unfold vectorWeakHaarEnergy
  rw [descendantsAverage_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact descendantsAverage_dualEnergy_le Q j (hG i)

/-- The residual of an H¹ function at depth `j` is bounded by the averaged
descendant weak-gradient energies. -/
theorem h1_residual_weak_bound (Q : TriadicCube 2) (j : ℕ)
    (u : H1Function (openCubeSet Q)) :
    energy Q (fun x => u.toFun x - cubeProjection Q j u.toFun x) ≤
      cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2 *
        (Real.sqrt 3) ^ j *
          vectorWeakHaarEnergy Q (fun x i => u.grad x i) := by
  have hu : MemLp u.toFun 2 (normalizedCubeMeasure Q) :=
    u.memL2_normalizedCubeMeasure
  have hG : ∀ i, MemLp (fun x => u.grad x i) 2 (normalizedCubeMeasure Q) :=
    u.grad_memL2_normalizedCubeMeasure
  have hres : MemLp (fun x => u.toFun x - cubeProjection Q j u.toFun x)
      2 (normalizedCubeMeasure Q) := hu.sub (projection_memLp Q j u.toFun 2)
  rw [energy_eq_descendantsAverage Q j hres]
  have hcell : ∀ U ∈ descendantsAtDepth Q j,
      energy U (fun x => u.toFun x - cubeProjection Q j u.toFun x) ≤
        (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2) *
          vectorWeakHaarEnergy U (fun x i => u.grad x i) := by
    intro U hU
    have heq : energy U (fun x => u.toFun x - cubeProjection Q j u.toFun x) =
        energy U (fun x => u.toFun x - cubeAverage U u.toFun) := by
      unfold energy pairing
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      beta_reduce
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth u.toFun hU hx]
    let uU := u.restrictToOpenSubcube hU
    have hlocal := h1_fluctuation_L2_bridge_sq U uU
    have hside : cubeScaleFactor U ^ 2 = cubeScaleFactor Q ^ 2 / 9 ^ j := by
      rw [cubeScaleFactor_descendant_eq_div_pow hU, div_pow]
      have h9 : (9 : ℝ) ^ j = ((3 : ℝ) ^ j) ^ 2 := by
        rw [← pow_mul, mul_comm j 2, pow_mul]
        norm_num
      rw [h9]
    have henergy : energy U (fun x => u.toFun x - cubeAverage U u.toFun) ≤
        cubeScaleFactor U ^ 2 * planarC0 ^ 2 *
          vectorWeakHaarEnergy U (fun x i => u.grad x i) := by
      have hnorm : vectorWeakHaarNorm U (fun x i => u.grad x i) ^ 2 =
          vectorWeakHaarEnergy U (fun x i => u.grad x i) := by
        rw [vectorWeakHaarNorm]
        exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U (fun x i => u.grad x i))
      simpa [uU, H1Function.restrictToOpenSubcube_toFun,
        H1Function.restrictToOpenSubcube_grad, h1ConstantOnCube_toFun, hnorm] using hlocal
    rw [heq]
    rw [hside] at henergy
    exact henergy
  have havg := descendantsAverage_vectorWeakEnergy_le Q j hG
  refine (descendantsAverage_le hcell).trans ?_
  calc
    descendantsAverage Q j (fun U =>
        (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2) *
          vectorWeakHaarEnergy U (fun x i => u.grad x i))
        = (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2) *
          descendantsAverage Q j (fun U =>
            vectorWeakHaarEnergy U (fun x i => u.grad x i)) := by
              rw [descendantsAverage_mul_left]
    _ ≤ (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2) *
          ((Real.sqrt 3) ^ j * vectorWeakHaarEnergy Q (fun x i => u.grad x i)) :=
            mul_le_mul_of_nonneg_left havg (by positivity)
    _ = cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2 *
          (Real.sqrt 3) ^ j * vectorWeakHaarEnergy Q (fun x i => u.grad x i) := by ring

/-- Exact positive-Haar Dirichlet bridge for zero-trace data. -/
theorem dirichlet_positiveHaar_bridge_sq (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    positiveHaarNorm Q u.toH1Function.toFun ^ 2 ≤
      cubeScaleFactor Q ^ 2 * planarFD ^ 2 *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) ^ 2 := by
  let q : ℝ := Real.sqrt 3
  let K : ℝ := vectorWeakHaarEnergy Q
    (fun x i => u.toH1Function.grad x i)
  let C : ℝ := cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K
  have hq1 : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hq2 : q ^ 2 = 3 := by
    dsimp [q]
    exact Real.sq_sqrt (by norm_num)
  have hratio : q ^ 2 / 9 = 1 / 3 := by rw [hq2]; norm_num
  have hK : 0 ≤ K := by
    dsimp [K]
    exact vectorWeakHaarEnergy_nonneg Q (fun x i => u.toH1Function.grad x i)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : MemLp u.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
    u.toH1Function.memL2_normalizedCubeMeasure
  have hG : ∀ i, MemLp (fun x => u.toH1Function.grad x i) 2
      (normalizedCubeMeasure Q) := u.toH1Function.grad_memL2_normalizedCubeMeasure
  have hroot : energy Q u.toH1Function.toFun ≤
      cubeScaleFactor Q ^ 2 * planarCD ^ 2 * K := by
    have h := dirichlet_L2_bridge_sq Q u
    have hnorm : vectorWeakHaarNorm Q
        (fun x i => u.toH1Function.grad x i) ^ 2 = K := by
      rw [vectorWeakHaarNorm]
      exact Real.sq_sqrt hK
    simpa [K, hnorm] using h
  have hterm : ∀ j : ℕ, q ^ j *
      energy Q (fun x => u.toH1Function.toFun x -
        cubeProjection Q j u.toH1Function.toFun x) ≤ C * (1 / 3 : ℝ) ^ j := by
    intro j
    have hres := h1_residual_weak_bound Q j u.toH1Function
    have hbound : 0 ≤ energy Q (fun x => u.toH1Function.toFun x -
        cubeProjection Q j u.toH1Function.toFun x) := energy_nonneg Q _
    calc
      q ^ j * energy Q (fun x => u.toH1Function.toFun x -
          cubeProjection Q j u.toH1Function.toFun x)
          ≤ q ^ j * (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2 *
              q ^ j * K) := by
                exact mul_le_mul_of_nonneg_left (by simpa [K] using hres)
                  (pow_nonneg hq0.le _)
      _ = C * (1 / 3 : ℝ) ^ j := by
            have hqpow : q ^ j * q ^ j = 3 ^ j := by
              rw [← mul_pow, ← pow_two, hq2]
            have h9 : (9 : ℝ) ^ j = (3 ^ j) ^ 2 := by
              rw [← pow_mul, mul_comm j 2, pow_mul]
              norm_num
            dsimp [C]
            calc
              q ^ j * (cubeScaleFactor Q ^ 2 / 9 ^ j * planarC0 ^ 2 * q ^ j * K) =
                  (cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K) *
                    ((q ^ j * q ^ j) / 9 ^ j) := by ring
              _ = (cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K) *
                    ((3 ^ j) / (3 ^ j) ^ 2) := by rw [hqpow, h9]
              _ = (cubeScaleFactor Q ^ 2 * planarC0 ^ 2 * K) *
                    (1 / 3 : ℝ) ^ j := by
                      congr 1
                      have h3j : (3 : ℝ) ^ j ≠ 0 :=
                        pow_ne_zero j (by norm_num)
                      rw [div_pow, one_pow]
                      field_simp [h3j]
  have hgeom : Summable (fun j : ℕ => C * (1 / 3 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C
  have hresSummable : Summable (fun j : ℕ => q ^ j *
      energy Q (fun x => u.toH1Function.toFun x -
        cubeProjection Q j u.toH1Function.toFun x)) := by
    apply hgeom.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs]
    have hnonneg : 0 ≤ q ^ j *
        energy Q (fun x => u.toH1Function.toFun x -
          cubeProjection Q j u.toH1Function.toFun x) :=
      mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
    rw [abs_of_nonneg hnonneg]
    exact hterm j
  have hgeomSum :
      (∑' j : ℕ, q ^ j * energy Q (fun x => u.toH1Function.toFun x -
        cubeProjection Q j u.toH1Function.toFun x)) ≤ C * (3 / 2 : ℝ) := by
    calc
      _ ≤ ∑' j : ℕ, C * (1 / 3 : ℝ) ^ j := hresSummable.tsum_le_tsum hterm hgeom
      _ = C * ∑' j : ℕ, (1 / 3 : ℝ) ^ j := by rw [tsum_mul_left]
      _ = C * (3 / 2 : ℝ) := by
            rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
            norm_num
  have habel := primalEnergy_eq_abel Q hq1 hf hresSummable
  have hCcoef : planarCD ^ 2 + (q - 1) * planarC0 ^ 2 * (3 / 2 : ℝ) =
      planarFD ^ 2 := by
    have hC1 : planarC1 ^ 2 = planarC0 ^ 2 - 1 / Real.pi ^ 2 := by
      linarith [planarC0_sq_eq_planarC1_sq_add]
    have hidentity : planarC0 ^ 2 * (1 + 3 * (q - 1) / 2) =
        4 / Real.pi ^ 2 := by
      simpa [q] using planarC0_exact_identity
    have hFD : planarFD ^ 2 = 7 / (2 * Real.pi ^ 2) := by
      rw [planarFD_exact, div_pow,
        Real.sq_sqrt (show 0 ≤ (7 / 2 : ℝ) by norm_num)]
      ring
    rw [planarCD_sq, hC1, hFD]
    field_simp [Real.pi_ne_zero] at hidentity ⊢
    nlinarith only [hidentity]
  have henergy : primalEnergy Q q u.toH1Function.toFun ≤
      cubeScaleFactor Q ^ 2 * planarFD ^ 2 * K := by
    rw [habel]
    have hqcoef : 0 ≤ q - 1 := by linarith
    calc
      energy Q u.toH1Function.toFun +
          (q - 1) * ∑' j : ℕ, q ^ j * energy Q
            (fun x => u.toH1Function.toFun x -
              cubeProjection Q j u.toH1Function.toFun x)
          ≤ cubeScaleFactor Q ^ 2 * planarCD ^ 2 * K +
              (q - 1) * (C * (3 / 2 : ℝ)) :=
            add_le_add hroot (mul_le_mul_of_nonneg_left hgeomSum hqcoef)
      _ = cubeScaleFactor Q ^ 2 * planarFD ^ 2 * K := by
            dsimp [C]
            rw [← hCcoef]
            ring_nf
  have hKnorm : vectorWeakHaarNorm Q
      (fun x i => u.toH1Function.grad x i) ^ 2 = K := by
    rw [vectorWeakHaarNorm]
    exact Real.sq_sqrt hK
  calc
    positiveHaarNorm Q u.toH1Function.toFun ^ 2 =
        primalEnergy Q q u.toH1Function.toFun := by
          rw [positiveHaarNorm]
          exact Real.sq_sqrt (primalEnergy_nonneg Q q (Real.sqrt_nonneg _) _)
    _ ≤ cubeScaleFactor Q ^ 2 * planarFD ^ 2 * K := henergy
    _ = cubeScaleFactor Q ^ 2 * planarFD ^ 2 *
          vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) ^ 2 := by
            rw [hKnorm]

/-- Norm form of the exact positive-Haar Dirichlet bridge for zero-trace data. -/
theorem dirichlet_positiveHaar_bridge (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) :
    positiveHaarNorm Q u.toH1Function.toFun ≤
      cubeScaleFactor Q * planarFD *
        vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
  have hsq := dirichlet_positiveHaar_bridge_sq Q u
  have hleft : 0 ≤ positiveHaarNorm Q u.toH1Function.toFun := Real.sqrt_nonneg _
  have hright : 0 ≤ cubeScaleFactor Q * planarFD *
      vectorWeakHaarNorm Q (fun x i => u.toH1Function.grad x i) := by
    exact mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le
      (by dsimp [planarFD]; positivity)) (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ hleft hright).mp (by simpa [mul_pow] using hsq)

end ASDExplicitGamma.Triadic

end
