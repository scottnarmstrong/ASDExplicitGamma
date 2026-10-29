module

public import ASDExplicitGamma.Cold.MatrixIndependentSum
public import ASDExplicitGamma.Cold.MatrixFrobeniusSum
public import ASDExplicitGamma.Cold.FourColorTwenty

/-! # The sharp four-colour matrix L2 estimate -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Sharp centered matrix L2 estimate for an arbitrary four-colour partition. Independence
is required only within each colour class, with arbitrary class populations. -/
theorem four_color_matrix_centered_sum {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] (color : ι → Fin 4) {n : Type*} [Fintype n] {Y : ι → Ω → Matrix n n ℝ} {M : ℝ}
    (hY : ∀ a i j, MemLp (fun ω => Y a ω i j) 2 ℙ)
    (hIndep : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => Y i.val) ℙ)
    (hCenter : ∀ a i j, (∫ ω, Y a ω i j ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i, matrixFrobeniusL2 ℙ (Y i) ≤ M) :
    matrixFrobeniusL2 ℙ (fun ω => ∑ i, Y i ω) ≤ 2*Real.sqrt (Fintype.card ι:ℝ)*M := by
  classical
  let N := fun c => Fintype.card {i // color i = c}
  let Z := fun (c : Fin 4) (ω : Ω) => ∑ i : {i // color i = c}, Y i.val ω
  have hclass (c : Fin 4) : matrixFrobeniusL2 ℙ (fun ω => Z c ω) ≤ Real.sqrt (N c:ℝ)*M := by
    exact matrixFrobeniusL2_independent_sum_le (Y := fun (a : {a // color a = c}) ω => Y a.val ω) (fun a => hY a.val) (hIndep c)
      (fun a => hCenter a.val) hM (fun a => hcap a.val)
  have hZ (c : Fin 4) (i j : n) : MemLp (fun ω => Z c ω i j) 2 ℙ := by
    simpa only [Z,Finset.sum_apply,Matrix.sum_apply] using memLp_finsetSum Finset.univ
      (fun a _ => hY (a : {a // color a = c}).val i j)
  have hsum := (matrixFrobeniusL2_sum_le Finset.univ (fun c _ => hZ c)).trans
    (Finset.sum_le_sum (fun c _ => hclass c))
  have heq : (fun ω => ∑ c, Z c ω) = (fun ω => ∑ a, Y a ω) := by
    funext ω
    exact Fintype.sum_fiberwise color (fun a => Y a ω)
  rw [heq] at hsum
  have hN : (∑ c : Fin 4, (N c:ℝ)) = (Fintype.card ι:ℝ) := by
    have he := Fintype.sum_fiberwise color (fun _ : ι => (1:ℝ))
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using he
  have hp := mul_le_mul_of_nonneg_left (four_color_population_bound N)
    hM
  rw [hN] at hp
  have he : (∑ c : Fin 4, Real.sqrt (N c:ℝ)*M) =
      (M)*(∑ c : Fin 4, Real.sqrt (N c:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [he] at hsum
  nlinarith only [hsum,hp]

/-- The source sharp `2/sqrt(N)` matrix average bound, without balanced populations. -/
theorem four_color_matrix_centered_average {Ω ι n : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] [Fintype n] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (color : ι → Fin 4) {Y : ι → Ω → Matrix n n ℝ} {M : ℝ}
    (hY : ∀ a i j, MemLp (fun ω => Y a ω i j) 2 ℙ)
    (hIndep : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => Y i.val) ℙ)
    (hCenter : ∀ a i j, (∫ ω, Y a ω i j ∂ℙ) = 0) (hM : 0 ≤ M)
    (hcap : ∀ i, matrixFrobeniusL2 ℙ (Y i) ≤ M) :
    matrixFrobeniusL2 ℙ (fun ω => (Fintype.card ι:ℝ)⁻¹ • ∑ i, Y i ω) ≤
      2/Real.sqrt (Fintype.card ι:ℝ)*M := by
  have hN : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [matrixFrobeniusL2_const_mul,abs_of_pos (inv_pos.mpr hN)]
  have hs := mul_le_mul_of_nonneg_left (four_color_matrix_centered_sum color hY hIndep hCenter hM hcap)
    (inv_nonneg.mpr hN.le)
  refine hs.trans_eq ?_
  have hr : 0 < Real.sqrt (Fintype.card ι:ℝ) := Real.sqrt_pos.mpr hN
  have he := Real.sq_sqrt hN.le
  field_simp
  rw [he]

end ASDExplicitGamma.Cold
