module
public import ASDExplicitGamma.Numerics.Native.TaylorArithmetic
public import ASDExplicitGamma.Numerics.Native.TaylorBound
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Real semantics of the sparse augmented systems and outward Taylor recursion. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

/-- Predecessor in the augmented state; row zero is separately fixed to zero. -/
def nativePrevious (i : Fin 21) : Fin 21 := ⟨i.val-1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

noncomputable def nativeSystemMatrix (s : NativeScaledSystem) : Matrix (Fin 21) (Fin 21) ℝ :=
  fun i j => if i.val=0 then 0 else
    (if j=i then (s.diag.getD i.val 0 : ℝ) else 0)+
    (if j=nativePrevious i then (s.subdiag.getD i.val 0 : ℝ) else 0)+
    (if j=0 then (s.force.getD i.val 0 : ℝ) else 0)

noncomputable def nativeVectorReal (v : List ℚ) : Fin 21 → ℝ :=
  fun i => (v.getD i.val 0 : ℝ)

theorem nativeSystemMatrix_mulVec (s : NativeScaledSystem) (v : Fin 21 → ℝ) (i : Fin 21) :
    (nativeSystemMatrix s *ᵥ v) i = if i.val=0 then 0 else
      (s.diag.getD i.val 0 : ℝ)*v i+
      (s.subdiag.getD i.val 0 : ℝ)*v (nativePrevious i)+
      (s.force.getD i.val 0 : ℝ)*v 0 := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  by_cases hi : i.val=0
  · simp only [nativeSystemMatrix, hi, ite_true, zero_mul, Finset.sum_const_zero]
  · simp only [nativeSystemMatrix, hi, ite_false, add_mul, Finset.sum_add_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem nativeSystemMatrix_nonneg (s : NativeScaledSystem)
    (hdiag : ∀ i : Fin 21, 0 ≤ s.diag.getD i.val 0)
    (hsub : ∀ i : Fin 21, 0 ≤ s.subdiag.getD i.val 0)
    (hforce : ∀ i : Fin 21, 0 ≤ s.force.getD i.val 0) :
    ∀ i j, 0 ≤ nativeSystemMatrix s i j := by
  intro i j
  have hd : (0 : ℝ) ≤ s.diag.getD i.val 0 := by exact_mod_cast hdiag i
  have hs : (0 : ℝ) ≤ s.subdiag.getD i.val 0 := by exact_mod_cast hsub i
  have hf : (0 : ℝ) ≤ s.force.getD i.val 0 := by exact_mod_cast hforce i
  simp only [nativeSystemMatrix]
  split_ifs <;> positivity

theorem nativeSystemMatrix_row_sum (s : NativeScaledSystem)
    (h : ∀ i : Fin 21, s.diag.getD i.val 0+s.subdiag.getD i.val 0+s.force.getD i.val 0 ≤ 6) :
    ∀ i, ∑ j, nativeSystemMatrix s i j ≤ 6 := by
  intro i
  have hm := nativeSystemMatrix_mulVec s (fun _ => 1) i
  simp only [Matrix.mulVec_apply_eq_sum, mul_one] at hm
  rw [hm]
  split_ifs
  · norm_num
  · have hr := (Rat.cast_le (K := ℝ)).2 (h i)
    simpa only [Rat.cast_add, Rat.cast_ofNat] using hr

/-- A rational matrix-vector operation is rounded upward once per nonzero row. -/
theorem nativeMatVec_getD (s : NativeScaledSystem) (v : List ℚ) (i : Fin 21) :
    (nativeMatVec s v).getD i.val 0 = if i.val=0 then 0 else
      nativeUp (s.diag.getD i.val 0*v.getD i.val 0+
        s.subdiag.getD i.val 0*v.getD (i.val-1) 0+s.force.getD i.val 0*v.getD 0 0) := by
  rcases i with ⟨i,hi⟩
  cases i with
  | zero => rfl
  | succ j =>
    have hj : j < 20 := by omega
    simp [nativeMatVec, List.getD_eq_getElem?_getD, hj]

theorem nativeMatVec_length (s : NativeScaledSystem) (v : List ℚ) :
    (nativeMatVec s v).length = 21 := by
  simp only [nativeMatVec, List.length_cons, List.length_map, List.length_range]

theorem nativeMatVec_upper (s : NativeScaledSystem) (v : List ℚ) (i : Fin 21) :
    (nativeSystemMatrix s *ᵥ nativeVectorReal v) i ≤ nativeVectorReal (nativeMatVec s v) i := by
  rw [nativeSystemMatrix_mulVec]
  simp only [nativeVectorReal, nativeMatVec_getD]
  split_ifs
  · simp only [Rat.cast_zero, le_refl]
  · have h := (Rat.cast_le (K := ℝ)).2 (nativeUp_ge
      (s.diag.getD i.val 0*v.getD i.val 0+s.subdiag.getD i.val 0*v.getD (i.val-1) 0+
        s.force.getD i.val 0*v.getD 0 0))
    simpa only [nativePrevious, Rat.cast_add, Rat.cast_mul, Fin.val_zero] using h

theorem nativeMatrix_mono {G : Matrix (Fin 21) (Fin 21) ℝ} (hG : ∀ i j, 0 ≤ G i j)
    {u v : Fin 21 → ℝ} (huv : ∀ i, u i ≤ v i) (i : Fin 21) :
    (G *ᵥ u) i ≤ (G *ᵥ v) i := by
  rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hG i j))

theorem nativeGetD_map (f : ℚ → ℚ) (v : List ℚ) (hv : v.length = 21) (i : Fin 21) :
    (v.map f).getD i.val 0 = f (v.getD i.val 0) := by
  have hi : i.val < v.length := by rw [hv]; exact i.isLt
  simp [List.getD_eq_getElem?_getD, hi]

theorem nativeGetD_zipAdd (u v : List ℚ) (hu : u.length = 21) (hv : v.length = 21)
    (i : Fin 21) :
    (List.zipWith (·+·) u v).getD i.val 0 = u.getD i.val 0+v.getD i.val 0 := by
  have hiu : i.val < u.length := by rw [hu]; exact i.isLt
  have hiv : i.val < v.length := by rw [hv]; exact i.isLt
  simp [List.getD_eq_getElem?_getD, hiu, hiv]

theorem nativeRoundedTerm_upper (s : NativeScaledSystem) (n : ℕ) (term : List ℚ)
    (u : Fin 21 → ℝ) (hG : ∀ i j, 0 ≤ nativeSystemMatrix s i j)
    (hu : ∀ i, u i ≤ nativeVectorReal term i) (i : Fin 21) :
    (nativeSystemMatrix s *ᵥ u) i/(n+1 : ℕ) ≤
      nativeVectorReal ((nativeMatVec s term).map fun x => nativeUp (x/(n+1 : ℕ))) i := by
  have hmv := (nativeMatrix_mono hG hu i).trans (nativeMatVec_upper s term i)
  have hn : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _
  have hdiv := div_le_div_of_nonneg_right hmv hn
  have hup := (Rat.cast_le (K := ℝ)).2 (nativeUp_ge ((nativeMatVec s term).getD i.val 0/(n+1 : ℕ)))
  have hmap := nativeGetD_map (fun x => nativeUp (x/(n+1 : ℕ))) (nativeMatVec s term)
    (nativeMatVec_length s term) i
  simp only [nativeVectorReal] at hdiv ⊢
  rw [hmap]
  apply hdiv.trans
  simpa only [Rat.cast_div, Rat.cast_natCast] using hup

theorem nativeExactTerm_succ (G : Matrix (Fin 21) (Fin 21) ℝ) (v : Fin 21 → ℝ) (n : ℕ) (i : Fin 21) :
    (G *ᵥ (fun j => (G^n *ᵥ v) j/(Nat.factorial n : ℝ))) i/(n+1 : ℕ) =
      (G^(n+1) *ᵥ v) i/(Nat.factorial (n+1) : ℝ) := by
  have hw : (fun j => (G^n *ᵥ v) j/(Nat.factorial n : ℝ)) =
      (1/(Nat.factorial n : ℝ)) • (G^n *ᵥ v) := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, one_div]
    ring
  rw [hw, Matrix.mulVec_smul, pow_succ', ← Matrix.mulVec_mulVec,
    Nat.factorial_succ, Nat.cast_mul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

noncomputable def nativeExactTerm (s : NativeScaledSystem) (v : Fin 21 → ℝ) (n : ℕ) (i : Fin 21) : ℝ :=
  (nativeSystemMatrix s^n *ᵥ v) i/(Nat.factorial n : ℝ)

noncomputable def nativeExactSum (s : NativeScaledSystem) (v : Fin 21 → ℝ) (n : ℕ) (i : Fin 21) : ℝ :=
  ∑ k ∈ Finset.range (n+1), nativeExactTerm s v k i

theorem nativeTaylorSteps_lengths (s : NativeScaledSystem) (fuel n : ℕ) (term accum : List ℚ)
    (ht : term.length = 21) (ha : accum.length = 21) :
    (nativeTaylorSteps s fuel n term accum).1.length = 21 ∧
    (nativeTaylorSteps s fuel n term accum).2.length = 21 := by
  induction fuel generalizing n term accum with
  | zero => exact ⟨ht,ha⟩
  | succ fuel ih =>
    simp only [nativeTaylorSteps]
    apply ih
    · simp only [List.length_map, nativeMatVec_length]
    · simp only [List.length_zipWith, List.length_map, nativeMatVec_length, ha, min_self]

theorem nativeTaylorSteps_bounds (s : NativeScaledSystem) (v : Fin 21 → ℝ)
    (hG : ∀ i j, 0 ≤ nativeSystemMatrix s i j) (fuel n : ℕ) (term accum : List ℚ)
    (ht : term.length = 21) (ha : accum.length = 21)
    (hterm : ∀ i, nativeExactTerm s v n i ≤ nativeVectorReal term i)
    (hacc : ∀ i, nativeExactSum s v n i ≤ nativeVectorReal accum i) :
    ∀ i, nativeExactTerm s v (n+fuel) i ≤ nativeVectorReal (nativeTaylorSteps s fuel n term accum).1 i ∧
      nativeExactSum s v (n+fuel) i ≤ nativeVectorReal (nativeTaylorSteps s fuel n term accum).2 i := by
  induction fuel generalizing n term accum with
  | zero => simpa only [Nat.add_zero, nativeTaylorSteps] using fun i => And.intro (hterm i) (hacc i)
  | succ fuel ih =>
    let term' := (nativeMatVec s term).map fun x => nativeUp (x/(n+1 : ℕ))
    let accum' := List.zipWith (·+·) accum term'
    have ht' : term'.length = 21 := by simp only [term', List.length_map, nativeMatVec_length]
    have ha' : accum'.length = 21 := by simp only [accum', List.length_zipWith, ha, ht', min_self]
    have hterm' (i : Fin 21) : nativeExactTerm s v (n+1) i ≤ nativeVectorReal term' i := by
      unfold nativeExactTerm
      rw [← nativeExactTerm_succ]
      exact nativeRoundedTerm_upper s n term (fun j => nativeExactTerm s v n j) hG hterm i
    have hacc' (i : Fin 21) : nativeExactSum s v (n+1) i ≤ nativeVectorReal accum' i := by
      have hn := hterm' i
      have ho := hacc i
      simp only [nativeExactSum, Finset.sum_range_succ] at ho ⊢
      simp only [nativeVectorReal, accum', nativeGetD_zipAdd accum term' ha ht' i, Rat.cast_add]
      exact add_le_add ho hn
    have hh := ih (n+1) term' accum' ht' ha' hterm' hacc'
    simpa only [nativeTaylorSteps, term', accum', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- The complete rounded polynomial dominates the exact positive Taylor polynomial. -/
theorem nativeTaylor_polynomial_upper (s : NativeScaledSystem) (hv : s.v.length=21)
    (hG : ∀ i j, 0 ≤ nativeSystemMatrix s i j) (i : Fin 21) :
    nativeExactSum s (nativeVectorReal s.v) 160 i ≤
      nativeVectorReal (nativeTaylorSteps s 160 0 s.v s.v).2 i := by
  have hterm (j : Fin 21) : nativeExactTerm s (nativeVectorReal s.v) 0 j ≤ nativeVectorReal s.v j := by
    simp only [nativeExactTerm, pow_zero, Matrix.one_mulVec, Nat.factorial_zero, Nat.cast_one, div_one, le_refl]
  have hsum (j : Fin 21) : nativeExactSum s (nativeVectorReal s.v) 0 j ≤ nativeVectorReal s.v j := by
    simpa only [nativeExactSum, Nat.zero_add, Finset.sum_range_one] using hterm j
  exact (nativeTaylorSteps_bounds s (nativeVectorReal s.v) hG 160 0 s.v s.v hv hv hterm hsum i).2

theorem nativeExactTerm_zero_row_succ (s : NativeScaledSystem) (v : Fin 21 → ℝ) (k : ℕ) :
    nativeExactTerm s v (k+1) 0 = 0 := by
  simp only [nativeExactTerm, pow_succ', ← Matrix.mulVec_mulVec, nativeSystemMatrix_mulVec,
    Fin.val_zero, ite_true, zero_div]

theorem nativeExactSum_zero_row (s : NativeScaledSystem) (v : Fin 21 → ℝ) (n : ℕ) :
    nativeExactSum s v n 0 = v 0 := by
  unfold nativeExactSum
  rw [Finset.sum_eq_single 0]
  · simp only [nativeExactTerm, pow_zero, Matrix.one_mulVec, Nat.factorial_zero, Nat.cast_one, div_one]
  · intro k hk hk0
    cases k with
    | zero => exact False.elim (hk0 rfl)
    | succ k => exact nativeExactTerm_zero_row_succ s v k
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem nativeSystemMatrix_exp_zero_row (s : NativeScaledSystem) (v : Fin 21 → ℝ) :
    (NormedSpace.exp (nativeSystemMatrix s) *ᵥ v) 0 = v 0 := by
  have hs := native_matrix_exp_hasSum (nativeSystemMatrix s) v 0
  rw [← hs.tsum_eq, tsum_eq_single 0]
  · simp only [pow_zero, Matrix.one_mulVec, Nat.factorial_zero, Nat.cast_one, div_one]
  · intro k hk0
    cases k with
    | zero => exact False.elim (hk0 rfl)
    | succ k => exact nativeExactTerm_zero_row_succ s v k

theorem nativeTaylorFinal_getD (accum : List ℚ) (ha : accum.length=21) (i : Fin 21) :
    (nativeTaylorFinal accum).getD i.val 0 = if i.val=0 then accum.getD 0 0 else
      nativeUp (accum.getD i.val 0+nativeExpTail) := by
  rcases i with ⟨i,hi⟩
  cases i with
  | zero => rfl
  | succ j =>
    simp [nativeTaylorFinal, List.getD_eq_getElem?_getD, ha, hi]

theorem nativeExpTail_cast :
    (nativeExpTail : ℝ) = (6^161/(Nat.factorial 161 : ℝ))/(1-6/162) := by
  simp only [nativeExpTail, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_sub,
    Rat.cast_one, Rat.cast_ofNat]

/-- The complete rounded vector, including the common remainder, encloses the real exponential. -/
theorem nativeTaylor_replay_sound (s : NativeScaledSystem) (hvl : s.v.length=21)
    (hdiag : ∀ i : Fin 21, 0 ≤ s.diag.getD i.val 0)
    (hsub : ∀ i : Fin 21, 0 ≤ s.subdiag.getD i.val 0)
    (hforce : ∀ i : Fin 21, 0 ≤ s.force.getD i.val 0)
    (hrow : ∀ i : Fin 21, s.diag.getD i.val 0+s.subdiag.getD i.val 0+s.force.getD i.val 0 ≤ 6)
    (hv : ∀ i : Fin 21, 0 ≤ s.v.getD i.val 0 ∧ s.v.getD i.val 0 ≤ 1) :
    ∀ i, (NormedSpace.exp (nativeSystemMatrix s) *ᵥ nativeVectorReal s.v) i ≤
      nativeVectorReal (nativeTaylorFinal (nativeTaylorSteps s 160 0 s.v s.v).2) i := by
  have hG := nativeSystemMatrix_nonneg s hdiag hsub hforce
  have hr := nativeSystemMatrix_row_sum s hrow
  have hvR (i : Fin 21) : 0 ≤ nativeVectorReal s.v i ∧ nativeVectorReal s.v i ≤ 1 := by
    change (0 : ℝ) ≤ (s.v.getD i.val 0 : ℝ) ∧ (s.v.getD i.val 0 : ℝ) ≤ 1
    constructor
    · exact_mod_cast (hv i).1
    · exact_mod_cast (hv i).2
  have hacc := (nativeTaylorSteps_lengths s 160 0 s.v s.v hvl hvl).2
  intro i
  have hpoly := nativeTaylor_polynomial_upper s hvl hG i
  simp only [nativeVectorReal, nativeTaylorFinal_getD _ hacc i]
  split_ifs with hi
  · have hiz : i=0 := Fin.ext hi
    subst i
    rw [nativeSystemMatrix_exp_zero_row]
    simpa only [nativeExactSum_zero_row, nativeVectorReal, Fin.val_zero] using hpoly
  · have he := native_matrix_exp_taylor_bound (nativeSystemMatrix s) (nativeVectorReal s.v)
      hG hr hvR i
    have hup := (Rat.cast_le (K := ℝ)).2 (nativeUp_ge
      (((nativeTaylorSteps s 160 0 s.v s.v).2).getD i.val 0+nativeExpTail))
    have htail := nativeExpTail_cast
    have hp : (∑ k ∈ Finset.range 161, (nativeSystemMatrix s^k *ᵥ nativeVectorReal s.v) i/(Nat.factorial k : ℝ)) ≤
        nativeVectorReal (nativeTaylorSteps s 160 0 s.v s.v).2 i := hpoly
    apply le_trans he
    apply le_trans (add_le_add hp (le_refl _))
    simpa only [Rat.cast_add, nativeVectorReal, htail] using hup

end ASDExplicitGamma.Numerics.Native
