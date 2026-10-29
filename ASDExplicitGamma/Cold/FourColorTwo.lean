module

public import ASDExplicitGamma.Gaussian.RioTwoSum
public import ASDExplicitGamma.Cold.FourColorTwenty

/-! # The sharp centered four-colour L2 estimate -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Sharp centered L2 estimate for an arbitrary four-colour partition. Independence
is required only within each colour class, with arbitrary class populations. -/
theorem four_color_two_centered_sum {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] (color : ι → Fin 4) {Y : ι → Ω → ℝ} {M : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 ℙ)
    (hIndep : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => Y i.val) ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i, lpNorm (Y i) 2 ℙ ≤ M) :
    lpNorm (∑ i, Y i) 2 ℙ ≤ 2*Real.sqrt (Fintype.card ι:ℝ)*M := by
  classical
  let N := fun c => Fintype.card {i // color i = c}
  let Z := fun (c : Fin 4) (ω : Ω) => ∑ i : {i // color i = c}, Y i.val ω
  have hZ (c : Fin 4) : MemLp (Z c) 2 ℙ :=
    memLp_finsetSum Finset.univ (fun i _ => hY i.val)
  have hclass (c : Fin 4) : lpNorm (Z c) 2 ℙ ≤ Real.sqrt (N c:ℝ)*M := by
    exact Gaussian.rio_lpNorm_two_sum_le (Y := fun (i : {i // color i = c}) ω => Y i.val ω) Finset.univ (fun i => hY i.val) (hIndep c)
      (fun i => hCenter i.val) hM (fun i _ => hcap i.val)
  have hsum := (lpNorm_sum_le (s := Finset.univ) (fun c _ => hZ c) (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans
    (Finset.sum_le_sum (fun c _ => hclass c))
  have heq : (∑ c, Z c) = ∑ i, Y i := by
    funext ω
    simp only [Finset.sum_apply]
    exact Fintype.sum_fiberwise color (fun i => Y i ω)
  rw [heq] at hsum
  have hN : (∑ c : Fin 4, (N c:ℝ)) = (Fintype.card ι:ℝ) := by
    have he := Fintype.sum_fiberwise color (fun _ : ι => (1:ℝ))
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using he
  have hp := mul_le_mul_of_nonneg_left (four_color_population_bound N)
    (show 0 ≤ M by positivity)
  rw [hN] at hp
  have he : (∑ c : Fin 4, Real.sqrt (N c:ℝ)*M) =
      (M)*(∑ c : Fin 4, Real.sqrt (N c:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he] at hsum
  nlinarith only [hsum,hp]

/-- The displayed `2*sqrt(19)/sqrt(N)` normalized four-colour bound. -/
theorem four_color_two_centered_average {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] (color : ι → Fin 4) {Y : ι → Ω → ℝ} {M : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 ℙ)
    (hIndep : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => Y i.val) ℙ)
    (hCenter : ∀ i, (∫ ω, Y i ω ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i, lpNorm (Y i) 2 ℙ ≤ M) :
    lpNorm (fun ω => (∑ i, Y i ω)/(Fintype.card ι:ℝ)) 2 ℙ ≤
      2/(Real.sqrt (Fintype.card ι:ℝ))*M := by
  classical
  have hn : Fintype.card ι ≠ 0 := Fintype.card_ne_zero
  have hN : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [lpNorm_fun_div_natCast hn]
  have hs := div_le_div_of_nonneg_right
    (four_color_two_centered_sum color hY hIndep hCenter hM hcap) hN.le
  have he : (fun ω => ∑ i, Y i ω) = ∑ i, Y i := by funext ω; simp only [Finset.sum_apply]
  rw [he]
  refine hs.trans_eq ?_
  have hroot : 0 < Real.sqrt (Fintype.card ι:ℝ) := Real.sqrt_pos.mpr hN
  have hsq := Real.sq_sqrt hN.le
  field_simp
  rw [hsq]
  ring

end ASDExplicitGamma.Cold
