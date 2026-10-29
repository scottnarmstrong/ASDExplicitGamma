module

public import ASDExplicitGamma.Cold.ColdMomentRecursion
public import ASDExplicitGamma.Cold.ColdPositiveFluctuation

/-! # Positive-fluctuation caps for the actual same-law hierarchy -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Every same-law source hierarchy has the transported positive-fluctuation bound;
the deterministic mean cap remains outside the positive part. -/
theorem ColdMomentSystem.positive_fluctuation {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (F : ColdMomentSystem Ω ℙ) {k ell : ℕ} (hk : k < ell)
    {M D : ℝ} (hM : 0 ≤ M) (hcap : lpNorm (F.trace k) 20 ℙ ≤ M)
    (hmean : (∫ ω, F.trace k ω ∂ℙ) ≤ D) :
    lpNorm (fun ω => max (F.trace ell ω-D) 0) 20 ℙ ≤ coldCenteredMomentCap M (ell-k) := by
  let instColdFluctChildrenNonempty : Nonempty (Fin (9^(ell-k))) :=
    Fin.pos_iff_nonempty.mp (pow_pos (by norm_num) _)
  let X := F.children k ell
  have hX (i : Fin (9^(ell-k))) : MemLp (X i) 20 ℙ :=
    (F.sameLaw k ell i).memLp_iff.mpr (F.trace_memLp k)
  have hn (i : Fin (9^(ell-k))) : ∀ᵐ ω ∂ℙ, 0 ≤ X i ω :=
    (F.sameLaw k ell i).symm.ae_mem_snd measurableSet_Ici (F.trace_nonneg k)
  have hXcap (i : Fin (9^(ell-k))) : lpNorm (X i) 20 ℙ ≤ M := by
    have he := congrArg ENNReal.toReal ((F.sameLaw k ell i).eLpNorm_eq (p := 20))
    exact he.trans_le hcap
  have hmean' : (∑ i, ∫ ω, X i ω ∂ℙ)/(Fintype.card (Fin (9^(ell-k))):ℝ) ≤ D := by
    dsimp only [X]
    simp_rw [(F.sameLaw k ell _).integral_eq]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ (by positivity : ((9^(ell-k):ℕ):ℝ) ≠ 0)]
    exact hmean
  have hfluct := cold_positive_fluctuation_cap (F.color k ell) hX hn (F.independent k ell hk) hM hXcap hmean'
  let A := fun ω => (∑ i, X i ω)/(Fintype.card (Fin (9^(ell-k))):ℝ)
  have hA : MemLp A 20 ℙ := by
    have hh := (memLp_finsetSum Finset.univ (fun i _ => hX i)).const_mul
      ((Fintype.card (Fin (9^(ell-k))):ℝ)⁻¹)
    simpa only [A,div_eq_mul_inv,mul_comm] using hh
  have hpos : MemLp (fun ω => max (A ω-D) 0) 20 ℙ := by
    exact (hA.sub (memLp_const D)).sup (memLp_const 0)
  have hmono : lpNorm (fun ω => max (F.trace ell ω-D) 0) 20 ℙ ≤ lpNorm (fun ω => max (A ω-D) 0) 20 ℙ := by
    apply cold_lpNorm_mono_ae hpos
    filter_upwards [F.subadditive k ell hk] with ω hω
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _),abs_of_nonneg (le_max_right _ _)]
    apply max_le_max_right
    simpa only [A,X,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using sub_le_sub_right hω D
  apply hmono.trans
  rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,cold_square_population_factor] at hfluct
  simpa only [A,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,coldCenteredMomentCap,ite_eq_right (Nat.ne_of_gt (Nat.sub_pos_of_lt hk))] using hfluct

end ASDExplicitGamma.Cold
