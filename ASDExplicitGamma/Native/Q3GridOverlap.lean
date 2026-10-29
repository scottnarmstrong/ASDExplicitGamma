module

public import ASDExplicitGamma.Native.SupportOverlap

/-! # Signed q3 support overlap on a triadic child grid -/

@[expose] public section

open Homogenization Set ASDExplicitGamma.Gaussian

namespace ASDExplicitGamma.Native

def q3GridAxisActive (s n : ℕ) (x : ℝ) (i : Fin (3^s)) : Prop :=
  (i.val : ℝ) - (3 : ℝ)^n / 2 ≤ x * (3 : ℝ)^s ∧
    x * (3 : ℝ)^s ≤ (i.val : ℝ) + 1 + (3 : ℝ)^n / 2

noncomputable def q3GridAxisActiveFinset (s n : ℕ) (x : ℝ) : Finset (Fin (3^s)) := by
  classical
  exact Finset.univ.filter (q3GridAxisActive s n x)

theorem q3GridAxisActiveFinset_card_le (s n : ℕ) (x : ℝ) :
    (q3GridAxisActiveFinset s n x).card ≤ 3^n + 2 := by
  classical
  let A := q3GridAxisActiveFinset s n x
  by_cases hA : A.Nonempty
  · let lo := A.min' hA
    let hi := A.max' hA
    have hlo : lo ∈ A := Finset.min'_mem A hA
    have hhi : hi ∈ A := Finset.max'_mem A hA
    have hdiam (i j : Fin (3^s)) (hiA : i ∈ A) (hjA : j ∈ A) :
        j.val ≤ i.val + 3^n + 1 := by
      have hiSpec : q3GridAxisActive s n x i := by
        simpa [A, q3GridAxisActiveFinset] using (Finset.mem_filter.mp hiA).2
      have hjSpec : q3GridAxisActive s n x j := by
        simpa [A, q3GridAxisActiveFinset] using (Finset.mem_filter.mp hjA).2
      have hreal : (j.val : ℝ) ≤ (i.val : ℝ) + (3 : ℝ)^n + 1 := by
        nlinarith [hiSpec.2, hjSpec.1]
      exact_mod_cast hreal
    have hdiam' : hi.val ≤ lo.val + 3^n + 1 := hdiam lo hi hlo hhi
    have hminmax : lo.val ≤ hi.val := Finset.le_max' A lo hlo
    have hsubset : A.image (fun i : Fin (3^s) => i.val) ⊆ Finset.Icc lo.val hi.val := by
      intro k hk
      obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hk
      simpa only [Finset.mem_Icc] using
        (show lo.val ≤ i.val ∧ i.val ≤ hi.val from
          ⟨Finset.min'_le A i hiA, Finset.le_max' A i hiA⟩)
    have hcardImage : (A.image (fun i : Fin (3^s) => i.val)).card = A.card := by
      exact Finset.card_image_iff.mpr (by
        intro a ha b hb hab
        exact Fin.ext hab)
    calc
      A.card = (A.image (fun i : Fin (3^s) => i.val)).card := hcardImage.symm
      _ ≤ (Finset.Icc lo.val hi.val).card := Finset.card_le_card hsubset
      _ = hi.val - lo.val + 1 := by simp [Nat.card_Icc]; omega
      _ ≤ 3^n + 2 := by omega
  · have hzero : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [A, hzero]


noncomputable def q3GridKernelScale (s n : ℕ) : {l : ℝ // 0 < l} :=
  ⟨(3 : ℝ)^n / (3 : ℝ)^s, by positivity⟩

noncomputable def q3GridExpandedSupport (s n : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) : Set (Vec 2) :=
  q3ExpandedRectangle
    ((ij.1.val : ℝ) / (3 : ℝ)^s) (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
    ((ij.2.val : ℝ) / (3 : ℝ)^s) (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s)
    (q3GridKernelScale s n)

theorem q3GridExpandedSupport_mem_iff (s n : ℕ)
    (ij : Fin (3^s) × Fin (3^s)) (x : Vec 2) :
    x ∈ q3GridExpandedSupport s n ij ↔
      q3GridAxisActive s n (x 0) ij.1 ∧ q3GridAxisActive s n (x 1) ij.2 := by
  have hK : 0 < (3 : ℝ)^s := by positivity
  have hleft (i : Fin (3^s)) :
      (i.val : ℝ) / (3 : ℝ)^s - ((3 : ℝ)^n / (3 : ℝ)^s) / 2 =
        ((i.val : ℝ) - (3 : ℝ)^n / 2) / (3 : ℝ)^s := by
    field_simp
  have hright (i : Fin (3^s)) :
      ((i.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s +
        ((3 : ℝ)^n / (3 : ℝ)^s) / 2 =
        ((i.val : ℝ) + 1 + (3 : ℝ)^n / 2) / (3 : ℝ)^s := by
    push_cast
    field_simp
  constructor
  · intro hx
    have hxrect :
        x 0 ∈ Set.Icc
            ((ij.1.val : ℝ) / (3 : ℝ)^s -
              ((3 : ℝ)^n / (3 : ℝ)^s) / 2)
            (((ij.1.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s +
              ((3 : ℝ)^n / (3 : ℝ)^s) / 2) ∧
        x 1 ∈ Set.Icc
            ((ij.2.val : ℝ) / (3 : ℝ)^s -
              ((3 : ℝ)^n / (3 : ℝ)^s) / 2)
            (((ij.2.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s +
              ((3 : ℝ)^n / (3 : ℝ)^s) / 2) := by
      simpa [q3GridExpandedSupport, q3GridKernelScale, q3ExpandedRectangle,
        Gaussian.closedRectangle] using hx
    constructor
    · constructor
      · apply (div_le_iff₀ hK).1
        simpa only [← hleft] using hxrect.1.1
      · apply (le_div_iff₀ hK).1
        simpa only [← hright] using hxrect.1.2
    · constructor
      · apply (div_le_iff₀ hK).1
        have haux : ((ij.2.val : ℝ) - (3 : ℝ)^n / 2) / (3 : ℝ)^s ≤ x 1 := by
          rw [← hleft]
          exact hxrect.2.1
        exact haux
      · apply (le_div_iff₀ hK).1
        have haux : x 1 ≤ ((ij.2.val : ℝ) + 1 + (3 : ℝ)^n / 2) / (3 : ℝ)^s := by
          rw [← hright]
          exact hxrect.2.2
        exact haux
  · rintro ⟨h0,h1⟩
    have hcoord (i : Fin (3^s)) (z : ℝ)
        (ha : (i.val : ℝ) - (3 : ℝ)^n / 2 ≤ z * (3 : ℝ)^s)
        (hb : z * (3 : ℝ)^s ≤ (i.val : ℝ) + 1 + (3 : ℝ)^n / 2) :
        z ∈ Set.Icc
          ((i.val : ℝ) / (3 : ℝ)^s - ((3 : ℝ)^n / (3 : ℝ)^s) / 2)
          (((i.val + 1 : ℕ) : ℝ) / (3 : ℝ)^s + ((3 : ℝ)^n / (3 : ℝ)^s) / 2) := by
      constructor
      · have haux := (div_le_iff₀ hK).2 ha
        simpa only [hleft] using haux
      · have haux := (le_div_iff₀ hK).2 hb
        simpa only [hright] using haux
    have hxrect := And.intro (hcoord ij.1 (x 0) h0.1 h0.2)
      (hcoord ij.2 (x 1) h1.1 h1.2)
    simpa [q3GridExpandedSupport, q3GridKernelScale, q3ExpandedRectangle,
      Gaussian.closedRectangle] using hxrect

noncomputable def q3GridActiveFinset (s n : ℕ) (x : Vec 2) :
    Finset (Fin (3^s) × Fin (3^s)) := by
  classical
  exact Finset.univ.filter (fun ij => x ∈ q3GridExpandedSupport s n ij)

theorem q3GridActiveFinset_card_le (s n : ℕ) (x : Vec 2) :
    (q3GridActiveFinset s n x).card ≤ (3^n + 2)^2 := by
  classical
  let A₀ := q3GridAxisActiveFinset s n (x 0)
  let A₁ := q3GridAxisActiveFinset s n (x 1)
  have hEq : q3GridActiveFinset s n x = A₀.product A₁ := by
    ext ij
    simp only [q3GridActiveFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    simp only [A₀, A₁, q3GridAxisActiveFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact q3GridExpandedSupport_mem_iff s n ij x
  rw [hEq, Finset.product_eq_sprod, Finset.card_product]
  have h₀ := q3GridAxisActiveFinset_card_le s n (x 0)
  have h₁ := q3GridAxisActiveFinset_card_le s n (x 1)
  have hprod := Nat.mul_le_mul h₀ h₁
  simpa [pow_two] using hprod


/-- The normalized multiplicity of q3-enlarged supports on an `s`-level
triadic grid, for a shell whose support side is `3^n` child widths. -/
noncomputable def q3GridOverlapFactor (s n : ℕ) : ℝ :=
  min 1 ((25 / 9 : ℝ) * (((3 : ℝ)^(s-n))^2)⁻¹)

theorem q3GridActiveFinset_card_ratio_le (s n : ℕ) (hn : 1 ≤ n) (hns : n ≤ s)
    (x : Vec 2) :
    ((q3GridActiveFinset s n x).card : ℝ) / ((3 : ℝ)^s)^2 ≤ q3GridOverlapFactor s n := by
  let U := q3GridActiveFinset s n x
  let K : ℝ := (3 : ℝ)^s
  let q : ℝ := (3 : ℝ)^n
  let r : ℝ := (3 : ℝ)^(s-n)
  have hK : 0 < K := by dsimp [K]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hN : 0 < K^2 := sq_pos_of_pos hK
  have hcardNnat : U.card ≤ (Finset.univ : Finset (Fin (3^s) × Fin (3^s))).card :=
    Finset.card_le_univ U
  have hcardN : (U.card : ℝ) ≤ K^2 := by
    have hnat : U.card ≤ (3^s)^2 := by simpa [pow_two] using hcardNnat
    dsimp [K]
    exact_mod_cast hnat
  have hcardq : (U.card : ℝ) ≤ (q + 2)^2 := by
    have hnat := q3GridActiveFinset_card_le s n x
    dsimp [U, q]
    exact_mod_cast hnat
  have hratioOne : (U.card : ℝ) / K^2 ≤ 1 :=
    (div_le_iff₀ hN).2 (by simpa using hcardN)
  have hnatadd : n + (s-n) = s := Nat.add_sub_of_le hns
  have hexp : s = n + (s-n) := hnatadd.symm
  have hpower : K = q * r := by
    calc
      K = (3 : ℝ)^(n + (s-n)) := by
        dsimp [K]
        exact congrArg (fun k : ℕ => (3 : ℝ)^k) hexp
      _ = q * r := by dsimp [q, r]; rw [pow_add]
  have hq3 : 3 ≤ q := by
    dsimp [q]
    cases n with
    | zero => omega
    | succ m =>
      simp only [pow_succ]
      have hp : (1 : ℝ) ≤ (3 : ℝ)^m := one_le_pow₀ (by norm_num)
      nlinarith
  have hshift : q + 2 ≤ (5 / 3 : ℝ) * q := by
    nlinarith [hq3]
  have hshiftSq : (q + 2)^2 ≤ ((5 / 3 : ℝ) * q)^2 := by
    have hsum : 0 ≤ ((5 / 3 : ℝ) * q) + (q + 2) := by positivity
    have hprod := mul_nonneg (sub_nonneg.mpr hshift) hsum
    nlinarith [hprod]
  have hquot : (q + 2)^2 / q^2 ≤ (25 / 9 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hq)).2
    nlinarith [hshiftSq]
  have hratioSmall : (U.card : ℝ) / K^2 ≤
      (25 / 9 : ℝ) * (r^2)⁻¹ := by
    have hnum : (U.card : ℝ) / K^2 ≤ (q + 2)^2 / K^2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hcardq (inv_nonneg.mpr (sq_nonneg K))
    have hden : (q + 2)^2 / K^2 = ((q + 2)^2 / q^2) * (r^2)⁻¹ := by
      rw [hpower]
      field_simp [hq.ne', hr.ne']
    calc
      (U.card : ℝ) / K^2 ≤ (q + 2)^2 / K^2 := hnum
      _ = ((q + 2)^2 / q^2) * (r^2)⁻¹ := hden
      _ ≤ (25 / 9 : ℝ) * (r^2)⁻¹ :=
        mul_le_mul_of_nonneg_right hquot (inv_nonneg.mpr (sq_nonneg r))
  dsimp [q3GridOverlapFactor, r]
  exact le_min hratioOne hratioSmall

end ASDExplicitGamma.Native
