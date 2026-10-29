module

public import ASDExplicitGamma.Scalar.DefectEnergyBound
public import ASDExplicitGamma.Gaussian.NonnegativeFatou

/-! Wick second-moment formula for a quadratic Gaussian defect source measured
in a positive-semidefinite symmetric bilinear form (the tiled positive-Haar
energy is such a form, not a Hilbert norm). Same proof as
`defectSource_gaussian_energy_formula`, with `inner` replaced by the form. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
open scoped BigOperators Topology
open Filter

/-- Symmetric positive-semidefinite bilinear form. -/
structure PsdForm (P : Type*) [AddCommGroup P] [Module ℝ P] where
  form : P →ₗ[ℝ] P →ₗ[ℝ] ℝ
  symm : ∀ a b, form a b = form b a
  nonneg : ∀ a, 0 ≤ form a a

namespace PsdForm

variable {P : Type*} [AddCommGroup P] [Module ℝ P] (β : PsdForm P)

theorem two_mul_le (a b : P) : 2 * β.form a b ≤ β.form a a + β.form b b := by
  have h := β.nonneg (a - b)
  simp only [map_sub, LinearMap.sub_apply] at h
  rw [β.symm b a] at h
  linarith

theorem sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → P) (g : κ → P) :
    β.form (∑ i ∈ s, f i) (∑ k ∈ t, g k) = ∑ i ∈ s, ∑ k ∈ t, β.form (f i) (g k) := by
  simp only [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]

end PsdForm

variable {P : Type*} [AddCommGroup P] [Module ℝ P]

/-- The finite quadratic defect source, in a bare module. -/
noncomputable def psdDefectSource {n : ℕ} (B : Fin n → Fin n → P) (x : Fin n → ℝ) : P :=
  ∑ i, ∑ j, (x i * x j) • B i j

theorem psdDefectSource_form_expansion {n : ℕ} (β : PsdForm P) (B : Fin n → Fin n → P)
    (x : Fin n → ℝ) :
    β.form (psdDefectSource B x) (psdDefectSource B x) =
      ∑ i, ∑ j, ∑ k, ∑ l, β.form (B i j) (B k l) * (x i * x j * (x k * x l)) := by
  unfold psdDefectSource
  rw [PsdForm.sum_sum]
  have key : ∀ i k : Fin n,
      β.form (∑ j, (x i * x j) • B i j) (∑ l, (x k * x l) • B k l) =
        ∑ j, ∑ l, β.form (B i j) (B k l) * (x i * x j * (x k * x l)) := by
    intro i k
    rw [PsdForm.sum_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  apply Finset.sum_congr rfl
  intro i _
  calc _ = ∑ k : Fin n, ∑ j : Fin n, ∑ l : Fin n,
          β.form (B i j) (B k l) * (x i * x j * (x k * x l)) :=
        Finset.sum_congr rfl (fun k _ => key i k)
    _ = _ := Finset.sum_comm

private theorem psd_diag_pairing {n : ℕ} (β : PsdForm P) (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if i = j ∧ k = l then β.form (B i j) (B k l) else 0) =
        β.form (∑ i, B i i) (∑ i, B i i) := by
  rw [PsdForm.sum_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro k _
    simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

private theorem psd_first_crossing {n : ℕ} (β : PsdForm P) (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if i = k ∧ j = l then β.form (B i j) (B k l) else 0) =
      ∑ i, ∑ j, β.form (B i j) (B i j) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro k _ hki
    simp [Ne.symm hki]
  · simp

private theorem psd_second_crossing {n : ℕ} (β : PsdForm P) (B : Fin n → Fin n → P) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      if i = l ∧ j = k then β.form (B i j) (B k l) else 0) =
      ∑ i, ∑ j, β.form (B i j) (B j i) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro k _ hkj
    simp [Ne.symm hkj]
  · simp

/-- Wick's three pairings give the exact second moment in the form. -/
theorem psdDefectSource_gaussian_energy_formula {n : ℕ} (β : PsdForm P)
    (B : Fin n → Fin n → P) :
    (∫ x, β.form (psdDefectSource B x) (psdDefectSource B x) ∂standardGaussianPi n) =
      β.form (∑ i, B i i) (∑ i, B i i) +
        ∑ i, ∑ j, β.form (B i j) (B i j) +
        ∑ i, ∑ j, β.form (B i j) (B j i) := by
  have hTerm (i j k l : Fin n) :
      Integrable (fun x : Fin n → ℝ => β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) := by
    have h := (integrable_gaussian_monomial [i,j,k,l]).const_mul (β.form (B i j) (B k l))
    have he : (fun x : Fin n → ℝ => β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) =
        fun x => β.form (B i j) (B k l) * gaussianMonomial [i,j,k,l] x := by
      funext x
      congr 1
      simp [gaussianMonomial]
      ring
    rw [he]
    exact h
  have hSumL (i j k : Fin n) :
      Integrable (fun x : Fin n → ℝ => ∑ l, β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) :=
    integrable_finsetSum _ (fun l _ => hTerm i j k l)
  have hSumK (i j : Fin n) :
      Integrable (fun x : Fin n → ℝ => ∑ k, ∑ l, β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) :=
    integrable_finsetSum _ (fun k _ => hSumL i j k)
  have hSumJ (i : Fin n) :
      Integrable (fun x : Fin n → ℝ => ∑ j, ∑ k, ∑ l, β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) :=
    integrable_finsetSum _ (fun j _ => hSumK i j)
  rw [show (fun x : Fin n → ℝ => β.form (psdDefectSource B x) (psdDefectSource B x)) =
      fun x => ∑ i, ∑ j, ∑ k, ∑ l,
        β.form (B i j) (B k l) * (x i * x j * (x k * x l)) by
      funext x
      exact psdDefectSource_form_expansion β B x]
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        ∫ x, β.form (B i j) (B k l) * (x i * x j * (x k * x l))
          ∂standardGaussianPi n := by
      rw [integral_finsetSum _ (fun i _ => hSumJ i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hSumK i j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun k _ => hSumL i j k)]
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_finsetSum _ (fun l _ => hTerm i j k l)]
    _ = ∑ i, ∑ j, ∑ k, ∑ l,
        β.form (B i j) (B k l) *
          ((if i = j ∧ k = l then 1 else 0) +
            (if i = k ∧ j = l then 1 else 0) +
            (if i = l ∧ j = k then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [integral_const_mul, standardGaussian_fourth_coordinate_moment]
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, mul_one]
      rw [psd_diag_pairing, psd_first_crossing, psd_second_crossing]

/-- The Wick bound in a positive-semidefinite form: row diagonal plus twice the
column sum. -/
theorem psdDefectSource_gaussian_energy_le {n : ℕ} (β : PsdForm P)
    (B : Fin n → Fin n → P) :
    (∫ x, β.form (psdDefectSource B x) (psdDefectSource B x) ∂standardGaussianPi n) ≤
      β.form (∑ i, B i i) (∑ i, B i i) + 2 * ∑ i, ∑ j, β.form (B i j) (B i j) := by
  rw [psdDefectSource_gaussian_energy_formula]
  have hx : (∑ i, ∑ j, β.form (B i j) (B j i)) ≤ ∑ i, ∑ j, β.form (B i j) (B i j) := by
    have h2 : 2 * (∑ i, ∑ j, β.form (B i j) (B j i)) ≤
        2 * ∑ i, ∑ j, β.form (B i j) (B i j) := by
      calc 2 * (∑ i, ∑ j, β.form (B i j) (B j i))
          = ∑ i, ∑ j, 2 * β.form (B i j) (B j i) := by
            simp only [Finset.mul_sum]
        _ ≤ ∑ i, ∑ j, (β.form (B i j) (B i j) + β.form (B j i) (B j i)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => β.two_mul_le _ _
        _ = 2 * ∑ i, ∑ j, β.form (B i j) (B i j) := by
            simp only [Finset.sum_add_distrib]
            rw [Finset.sum_comm (f := fun i j => β.form (B j i) (B j i))]
            ring
    linarith
  linarith

theorem psdDefectSource_form_continuous {n : ℕ} (β : PsdForm P) (B : Fin n → Fin n → P) :
    Continuous (fun x : Fin n → ℝ => β.form (psdDefectSource B x) (psdDefectSource B x)) := by
  have : (fun x : Fin n → ℝ => β.form (psdDefectSource B x) (psdDefectSource B x)) =
      fun x => ∑ i, ∑ j, ∑ k, ∑ l, β.form (B i j) (B k l) * (x i * x j * (x k * x l)) := by
    funext x
    exact psdDefectSource_form_expansion β B x
  rw [this]
  fun_prop

theorem psdDefectSource_form_integrable {n : ℕ} (β : PsdForm P) (B : Fin n → Fin n → P) :
    Integrable (fun x : Fin n → ℝ => β.form (psdDefectSource B x) (psdDefectSource B x))
      (standardGaussianPi n) := by
  have hTerm (i j k l : Fin n) :
      Integrable (fun x : Fin n → ℝ => β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) (standardGaussianPi n) := by
    have h := (integrable_gaussian_monomial [i,j,k,l]).const_mul (β.form (B i j) (B k l))
    have he : (fun x : Fin n → ℝ => β.form (B i j) (B k l) *
        (x i * x j * (x k * x l))) =
        fun x => β.form (B i j) (B k l) * gaussianMonomial [i,j,k,l] x := by
      funext x
      congr 1
      simp [gaussianMonomial]
      ring
    rw [he]
    exact h
  have : (fun x : Fin n → ℝ => β.form (psdDefectSource B x) (psdDefectSource B x)) =
      fun x => ∑ i, ∑ j, ∑ k, ∑ l, β.form (B i j) (B k l) * (x i * x j * (x k * x l)) := by
    funext x
    exact psdDefectSource_form_expansion β B x
  rw [this]
  refine integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hTerm i j k l))))

end ASDExplicitGamma.Scalar
