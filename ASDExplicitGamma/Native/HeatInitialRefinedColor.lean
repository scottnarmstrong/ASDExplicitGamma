module

public import ASDExplicitGamma.Cold.FourColorTwenty
public import ASDExplicitGamma.Cold.NativeFourColor
public import ASDExplicitGamma.Cold.NativeLocalTrace

/-! Finite-range colouring at the refined cutoff: scale-`m` cells whose
integer coordinates agree modulo four are at distance at least `3^(m+1)`, so
the cutoff-`(m+1)` local observables are independent within a colour class. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The sixteen residue classes of the two integer cell coordinates modulo four. -/
def coldRefinedColor (Q : TriadicCube 2) : Fin 4 × Fin 4 :=
  (⟨(Q.index 0 % 4).toNat, by
      have h0 := Int.emod_nonneg (Q.index 0) (by norm_num : (4 : ℤ) ≠ 0)
      have h0' := Int.emod_lt_of_pos (Q.index 0) (by norm_num : (0 : ℤ) < 4)
      omega⟩,
    ⟨(Q.index 1 % 4).toNat, by
      have h1 := Int.emod_nonneg (Q.index 1) (by norm_num : (4 : ℤ) ≠ 0)
      have h1' := Int.emod_lt_of_pos (Q.index 1) (by norm_num : (0 : ℤ) < 4)
      omega⟩)

theorem coldRefinedColor_mod {Q R : TriadicCube 2}
    (h : coldRefinedColor Q = coldRefinedColor R) (i : Fin 2) :
    Q.index i % 4 = R.index i % 4 := by
  have hQ0 := Int.emod_nonneg (Q.index 0) (by norm_num : (4 : ℤ) ≠ 0)
  have hQ1 := Int.emod_nonneg (Q.index 1) (by norm_num : (4 : ℤ) ≠ 0)
  have hR0 := Int.emod_nonneg (R.index 0) (by norm_num : (4 : ℤ) ≠ 0)
  have hR1 := Int.emod_nonneg (R.index 1) (by norm_num : (4 : ℤ) ≠ 0)
  have h0 := congrArg (fun p : Fin 4 × Fin 4 => p.1.val) h
  have h1 := congrArg (fun p : Fin 4 × Fin 4 => p.2.val) h
  simp only [coldRefinedColor] at h0 h1
  fin_cases i
  · change Q.index 0 % 4 = R.index 0 % 4
    omega
  · change Q.index 1 % 4 = R.index 1 % 4
    omega

/-- Distinct same-scale cells of one refined colour are separated by three cell
sides in some coordinate. -/
theorem cold_refined_color_separation {Q R : TriadicCube 2}
    (hscale : Q.scale = R.scale) (hneq : Q ≠ R)
    (hcolor : coldRefinedColor Q = coldRefinedColor R)
    {x y : Vec 2} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet R) :
    ∃ k : Fin 2, (3 : ℝ) ^ (Q.scale + 1) ≤ |(x - y) k| := by
  have hidx : ∃ k : Fin 2, Q.index k ≠ R.index k := by
    by_contra hn
    push Not at hn
    have he : Q.index = R.index := funext hn
    apply hneq
    cases Q
    cases R
    simp_all
  obtain ⟨i, hi⟩ := hidx
  have hp := coldRefinedColor_mod hcolor i
  have hd : Q.index i + 4 ≤ R.index i ∨ R.index i + 4 ≤ Q.index i := by omega
  have hs : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have h3 : (3 : ℝ) ^ (Q.scale + 1) = 3 * (3 : ℝ) ^ Q.scale := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring
  have hxlo := (hx i).1
  have hxhi := (hx i).2.le
  have hylo := (hy i).1
  have hyhi := (hy i).2.le
  simp only [cubeScaleFactor, ← hscale] at hxlo hxhi hylo hyhi
  refine ⟨i, ?_⟩
  rw [h3]
  rcases hd with hd | hd
  · have hreal : (Q.index i : ℝ) + 4 ≤ (R.index i : ℝ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hreal hs.le
    have hgap : 3 * (3 : ℝ) ^ Q.scale ≤ y i - x i := by nlinarith only [hm, hxhi, hylo]
    exact hgap.trans (by simpa only [Pi.sub_apply, neg_sub] using neg_le_abs (x i - y i))
  · have hreal : (R.index i : ℝ) + 4 ≤ (Q.index i : ℝ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hreal hs.le
    have hgap : 3 * (3 : ℝ) ^ Q.scale ≤ x i - y i := by nlinarith only [hm, hyhi, hxlo]
    exact hgap.trans (le_abs_self _)

/-- Cutoff-`(m+1)` local observables of scale-`m` cells are independent within
a refined colour class. -/
theorem cold_refined_color_independent {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    (C : ι → TriadicCube 2) (hC : Function.Injective C)
    (hscale : ∀ i, (C i).scale = m)
    {X : ∀ i, Cutoff.CutoffSample 2 → E i}
    (hX : ∀ i, @Measurable (Cutoff.CutoffSample 2) (E i)
      (Cutoff.cutoffSampleLocalSigma M (m + 1) (cubeSet (C i))) _ (X i)) :
    ∀ c : Fin 4 × Fin 4, ProbabilityTheory.iIndepFun
      (fun i : {i // coldRefinedColor (C i) = c} => X i.val)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  intro c
  apply cold_iIndepFun_cutoffLocal M h hM (m + 1)
    (fun i : {i // coldRefinedColor (C i) = c} => cubeSet (C i.val))
    (fun i => measurableSet_cubeSet (C i.val))
  · intro i j hij x hx y hy
    have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    have hneq : C i.val ≠ C j.val := fun he => hval (hC he)
    have hsc : (C i.val).scale = (C j.val).scale := (hscale _).trans (hscale _).symm
    obtain ⟨k, hk⟩ := cold_refined_color_separation hsc hneq
      (i.property.trans j.property.symm) hx hy
    exact ⟨k, by rw [hscale] at hk; exact hk⟩
  · intro i
    exact hX i.val

/-- Sharp centered L20 estimate for an arbitrary finite colour partition. -/
theorem color_twenty_centered_sum {Ω ι κ : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsFiniteMeasure ℙ] [Fintype ι] [Fintype κ] [DecidableEq κ] (color : ι → κ)
    {Y : ι → Ω → ℝ} {M : ℝ}
    (hY : ∀ i, MemLp (Y i) 20 ℙ)
    (hIndep : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => Y i.val) ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i, lpNorm (Y i) 20 ℙ ≤ M) :
    lpNorm (∑ i, Y i) 20 ℙ ≤
      Real.sqrt 19 * Real.sqrt (Fintype.card κ : ℝ) *
        Real.sqrt (Fintype.card ι : ℝ) * M := by
  classical
  let N := fun c => Fintype.card {i // color i = c}
  let Z := fun c : κ => ∑ i : {i // color i = c}, Y i.val
  have hZ (c : κ) : MemLp (Z c) 20 ℙ :=
    memLp_finsetSum' Finset.univ (fun i _ => hY i.val)
  have hclass (c : κ) : lpNorm (Z c) 20 ℙ ≤ Real.sqrt 19 * Real.sqrt (N c : ℝ) * M := by
    exact Gaussian.rio_lpNorm_twenty_sum_le Finset.univ (fun i => hY i.val) (hIndep c)
      (fun i => hCenter i.val) hM (fun i _ => hcap i.val)
  have hsum := (lpNorm_sum_le (s := Finset.univ) (fun c _ => hZ c)
    (by norm_num : (1 : ℝ≥0∞) ≤ 20)).trans
    (Finset.sum_le_sum (fun c _ => hclass c))
  have heq : (∑ c, Z c) = ∑ i, Y i := Fintype.sum_fiberwise color Y
  rw [heq] at hsum
  have hN : (∑ c : κ, (N c : ℝ)) = (Fintype.card ι : ℝ) := by
    have he := Fintype.sum_fiberwise color (fun _ : ι => (1 : ℝ))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using he
  have hpop : (∑ c : κ, Real.sqrt (N c : ℝ)) ≤
      Real.sqrt (Fintype.card κ : ℝ) * Real.sqrt (Fintype.card ι : ℝ) := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1 : ℝ))
      (fun c => Real.sqrt (N c : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcs
    simp_rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hcs
    rw [hN, mul_one] at hcs
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le hcs
  have hp := mul_le_mul_of_nonneg_left hpop (show 0 ≤ Real.sqrt 19 * M by positivity)
  have he : (∑ c : κ, Real.sqrt 19 * Real.sqrt (N c : ℝ) * M) =
      (Real.sqrt 19 * M) * (∑ c : κ, Real.sqrt (N c : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he] at hsum
  nlinarith only [hsum, hp]

end ASDExplicitGamma.Cold

end
