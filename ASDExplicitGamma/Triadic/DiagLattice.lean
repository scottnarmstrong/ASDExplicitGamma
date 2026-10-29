module

public import ASDExplicitGamma.Triadic.DiagCertificates
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Real-space contraction of the joint weak-face lattice row. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open scoped BigOperators

noncomputable section

/-- A permutation shift gives the lattice row in source equation (3.1). -/
def diagLatticeRow {ι : Type*} (S : Equiv.Perm ι) (σ : ℝ) (a e : ι → ℝ) (i : ι) : ℝ :=
  (a i + a (S i)) / 2 + σ * (e i - e (S i))

/-- The adjoint row is pointwise contractive when σ² ≤ 1/4. -/
theorem diagLatticeRow_adjoint_pointwise {σ x y : ℝ} (hσ : σ ^ 2 ≤ 1 / 4) :
    ((x + y) / 2) ^ 2 + (σ * (x - y)) ^ 2 ≤ (x ^ 2 + y ^ 2) / 2 := by
  have h := mul_nonneg (sub_nonneg.mpr hσ) (sq_nonneg (x - y))
  nlinarith only [h]

/-- Shifting a summand moves the shift to its test function with inverse sign. -/
theorem diagLattice_shift_pairing {ι : Type*} [Fintype ι]
    (S : Equiv.Perm ι) (a h : ι → ℝ) :
    (∑ i, a (S i) * h i) = ∑ i, a i * h (S.symm i) := by
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp S (fun i => a i * h (S.symm i)))

/-- Exact adjoint pairing; no decorrelation of the two face functionals. -/
theorem diagLatticeRow_pairing {ι : Type*} [Fintype ι]
    (S : Equiv.Perm ι) (σ : ℝ) (a e h : ι → ℝ) :
    (∑ i, diagLatticeRow S σ a e i * h i) =
      ∑ i, (a i * ((h i + h (S.symm i)) / 2) +
        e i * (σ * (h i - h (S.symm i)))) := by
  have hleft (i : ι) : diagLatticeRow S σ a e i * h i =
      (a i * h i + a (S i) * h i) / 2 + σ * (e i * h i - e (S i) * h i) := by
    unfold diagLatticeRow
    ring
  have hright (i : ι) :
      a i * ((h i + h (S.symm i)) / 2) + e i * (σ * (h i - h (S.symm i))) =
      (a i * h i + a i * h (S.symm i)) / 2 + σ * (e i * h i - e i * h (S.symm i)) := by ring
  simp only [hleft, hright, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.mul_sum]
  rw [diagLattice_shift_pairing S a h, diagLattice_shift_pairing S e h]

/-- Constant-one joint row contraction on any finite periodic lattice.
This replaces DIAG's older triangle bound 2*c_face. -/
theorem diagLatticeRow_contracts {ι : Type*} [Fintype ι]
    (S : Equiv.Perm ι) {σ : ℝ} (hσ : σ ^ 2 ≤ 1 / 4) (a e : ι → ℝ) :
    (∑ i, diagLatticeRow S σ a e i ^ 2) ≤ ∑ i, (a i ^ 2 + e i ^ 2) := by
  let h := diagLatticeRow S σ a e
  have hadj : (∑ i, (((h i + h (S.symm i)) / 2) ^ 2 +
      (σ * (h i - h (S.symm i))) ^ 2)) ≤ ∑ i, h i ^ 2 := by
    calc
      _ ≤ ∑ i, (h i ^ 2 + h (S.symm i) ^ 2) / 2 :=
        Finset.sum_le_sum fun _ _ => diagLatticeRow_adjoint_pointwise hσ
      _ = ∑ i, h i ^ 2 := by
        have hshift : (∑ i, h (S.symm i) ^ 2) = ∑ i, h i ^ 2 :=
          Equiv.sum_comp S.symm (fun i => h i ^ 2)
        rw [← Finset.sum_div, Finset.sum_add_distrib, hshift]
        ring
  have hpoint : ∀ i, 2 * (a i * ((h i + h (S.symm i)) / 2) +
      e i * (σ * (h i - h (S.symm i)))) ≤
        a i ^ 2 + e i ^ 2 + ((h i + h (S.symm i)) / 2) ^ 2 +
          (σ * (h i - h (S.symm i))) ^ 2 := by
    intro i
    nlinarith only [sq_nonneg (a i - (h i + h (S.symm i)) / 2),
      sq_nonneg (e i - σ * (h i - h (S.symm i)))]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hpoint i
  have hpair := diagLatticeRow_pairing S σ a e h
  have hid : (∑ i, diagLatticeRow S σ a e i * h i) = ∑ i, h i ^ 2 := by
    simp only [h, pow_two]
  rw [hid] at hpair
  have hsum' : 2 * ∑ i, h i ^ 2 ≤
      (∑ i, (a i ^ 2 + e i ^ 2)) +
        ∑ i, (((h i + h (S.symm i)) / 2) ^ 2 + (σ * (h i - h (S.symm i))) ^ 2) := by
    calc
      _ = ∑ i, 2 * (a i * ((h i + h (S.symm i)) / 2) +
          e i * (σ * (h i - h (S.symm i)))) := by rw [hpair, Finset.mul_sum]
      _ ≤ _ := by
        simpa only [Finset.sum_add_distrib, add_assoc] using hsum
  change (∑ i, h i ^ 2) ≤ _
  linarith only [hadj, hsum']

end

end ASDExplicitGamma.Triadic
