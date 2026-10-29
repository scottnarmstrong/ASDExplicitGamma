module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-! Abstract Hilbert transposition: a family of linear maps `T l : V → H` that are bounded by a
seminorm `‖ψ v‖` with row and column bounds has a family of continuous maps `A l : H → H` with
`⟪A l y, ψ v⟫ = ⟪T l v, y⟫` and the transposed column and row bounds (the minimum-norm
extension of the source's potential slot, `relative_growth_interpolant_paired_covariance.md`
(2.3), (3.2)). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open scoped InnerProductSpace BigOperators Topology
open Filter

section

variable {V ι H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- `S ≤ c √S` with `c ≥ 0` forces `S ≤ c²`. -/
theorem le_sq_of_le_mul_sqrt' {S c : ℝ} (hS : 0 ≤ S) (hc : 0 ≤ c)
    (h : S ≤ c * Real.sqrt S) : S ≤ c ^ 2 := by
  have ht := Real.sqrt_nonneg S
  have hs := Real.sq_sqrt hS
  by_cases h0 : Real.sqrt S = 0
  · have : S = 0 := by rw [← hs, h0]; ring
    rw [this]; positivity
  · have hpos : 0 < Real.sqrt S := lt_of_le_of_ne ht (Ne.symm h0)
    have : Real.sqrt S ≤ c := by
      by_contra hlt
      have hlt := not_le.mp hlt
      nlinarith
    nlinarith

/-- **Abstract Hilbert transposition.** -/
theorem hilbert_transpose (ψ : V →ₗ[ℝ] H) (T : ι → V →ₗ[ℝ] H) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcol : ∀ (s : Finset ι) (v : V), ∑ l ∈ s, ‖T l v‖ ^ 2 ≤ b ^ 2 * ‖ψ v‖ ^ 2)
    (hrow : ∀ (s : Finset ι) (v : ι → V),
      ‖∑ l ∈ s, T l (v l)‖ ^ 2 ≤ a ^ 2 * ∑ l ∈ s, ‖ψ (v l)‖ ^ 2) :
    ∃ A : ι → H →L[ℝ] H,
      (∀ l y v, ⟪A l y, ψ v⟫_ℝ = ⟪T l v, y⟫_ℝ) ∧
      (∀ (s : Finset ι) y, ∑ l ∈ s, ‖A l y‖ ^ 2 ≤ a ^ 2 * ‖y‖ ^ 2) ∧
      (∀ (s : Finset ι) (y : ι → H), ‖∑ l ∈ s, A l (y l)‖ ^ 2 ≤ b ^ 2 * ∑ l ∈ s, ‖y l‖ ^ 2) := by
  classical
  let E : Submodule ℝ H := (LinearMap.range ψ).topologicalClosure
  have : CompleteSpace E := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let ψE : V →ₗ[ℝ] E := ψ.codRestrict E (fun v =>
    (LinearMap.range ψ).le_topologicalClosure ⟨v, rfl⟩)
  have hψE : ∀ v, ‖ψE v‖ = ‖ψ v‖ := fun v => rfl
  have hdense : DenseRange ψE := by
    rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
    intro x
    refine closure_mono ?_ x.2
    rintro z ⟨v, hv⟩
    exact ⟨ψE v, ⟨v, rfl⟩, hv⟩
  have hb1 : ∀ l v, ‖T l v‖ ≤ b * ‖ψE v‖ := by
    intro l v
    have h := hcol {l} v
    simp only [Finset.sum_singleton] at h
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (by rw [mul_pow, hψE]; exact h)
  let Tt : ι → E →L[ℝ] H := fun l => (T l).extendOfNorm ψE
  have htt : ∀ l v, Tt l (ψE v) = T l v := fun l v =>
    LinearMap.extendOfNorm_eq hdense ⟨b, hb1 l⟩ v
  have hcolE : ∀ (s : Finset ι) (x : E), ∑ l ∈ s, ‖Tt l x‖ ^ 2 ≤ b ^ 2 * ‖x‖ ^ 2 := by
    intro s x
    refine DenseRange.induction_on hdense x (isClosed_le ?_ ?_) (fun v => ?_)
    · exact continuous_finsetSum _ fun l _ => ((Tt l).continuous.norm).pow 2
    · exact continuous_const.mul (continuous_norm.pow 2)
    · simpa only [htt, hψE] using hcol s v
  have hrowE : ∀ (s : Finset ι) (x : ι → E),
      ‖∑ l ∈ s, Tt l (x l)‖ ^ 2 ≤ a ^ 2 * ∑ l ∈ s, ‖x l‖ ^ 2 := by
    intro s x
    have hd : DenseRange (Pi.map (fun _ : ι => ψE)) := DenseRange.piMap (fun _ => hdense)
    refine DenseRange.induction_on hd x (isClosed_le ?_ ?_) (fun v => ?_)
    · exact (continuous_finsetSum _ fun l _ =>
        (Tt l).continuous.comp (continuous_apply l)).norm.pow 2
    · exact continuous_const.mul (continuous_finsetSum _ fun l _ =>
        ((continuous_apply l).norm).pow 2)
    · simpa only [Pi.map_apply, htt, hψE] using hrow s v
  refine ⟨fun l => E.subtypeL.comp (ContinuousLinearMap.adjoint (Tt l)), ?_, ?_, ?_⟩
  · intro l y v
    change ⟪((ContinuousLinearMap.adjoint (Tt l)) y : E), (ψE v : E)⟫_ℝ = _
    rw [ContinuousLinearMap.adjoint_inner_left, htt, real_inner_comm]
  · intro s y
    set x : ι → E := fun l => (ContinuousLinearMap.adjoint (Tt l)) y with hx
    have hnorm : ∀ l, ‖(E.subtypeL.comp (ContinuousLinearMap.adjoint (Tt l))) y‖ = ‖x l‖ :=
      fun l => rfl
    simp only [hnorm]
    set S : ℝ := ∑ l ∈ s, ‖x l‖ ^ 2 with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun l _ => by positivity
    have h1 : S = ⟪y, ∑ l ∈ s, Tt l (x l)⟫_ℝ := by
      rw [hS, inner_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← ContinuousLinearMap.adjoint_inner_left, ← real_inner_self_eq_norm_sq]
    have h2 : ‖∑ l ∈ s, Tt l (x l)‖ ≤ a * Real.sqrt S := by
      have := hrowE s x
      rw [← hS] at this
      calc ‖∑ l ∈ s, Tt l (x l)‖ ≤ Real.sqrt (a ^ 2 * S) := by
            rw [← Real.sqrt_sq (norm_nonneg _)]
            exact Real.sqrt_le_sqrt this
        _ = a * Real.sqrt S := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ha]
    have h3 : S ≤ (a * ‖y‖) * Real.sqrt S := by
      calc S = ⟪y, ∑ l ∈ s, Tt l (x l)⟫_ℝ := h1
        _ ≤ ‖y‖ * ‖∑ l ∈ s, Tt l (x l)‖ := real_inner_le_norm _ _
        _ ≤ ‖y‖ * (a * Real.sqrt S) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (a * ‖y‖) * Real.sqrt S := by ring
    have := le_sq_of_le_mul_sqrt' hS0 (by positivity) h3
    calc S ≤ (a * ‖y‖) ^ 2 := this
      _ = a ^ 2 * ‖y‖ ^ 2 := by ring
  · intro s y
    set w : E := ∑ l ∈ s, (ContinuousLinearMap.adjoint (Tt l)) (y l) with hw
    have hnorm : ‖∑ l ∈ s, (E.subtypeL.comp (ContinuousLinearMap.adjoint (Tt l))) (y l)‖ =
        ‖w‖ := by
      have : ∑ l ∈ s, (E.subtypeL.comp (ContinuousLinearMap.adjoint (Tt l))) (y l) = (w : H) := by
        rw [hw]; simp
      rw [this]; rfl
    rw [hnorm]
    set Y : ℝ := ∑ l ∈ s, ‖y l‖ ^ 2 with hY
    have hw2 : ‖w‖ ^ 2 = ∑ l ∈ s, ⟪y l, Tt l w⟫_ℝ := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [hw]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    set P : ℝ := ∑ l ∈ s, ‖y l‖ * ‖Tt l w‖ with hP
    have hwP : ‖w‖ ^ 2 ≤ P := by
      rw [hw2]
      exact Finset.sum_le_sum fun l _ => real_inner_le_norm _ _
    have hPY : P ^ 2 ≤ Y * (b ^ 2 * ‖w‖ ^ 2) := by
      calc P ^ 2 ≤ (∑ l ∈ s, ‖y l‖ ^ 2) * ∑ l ∈ s, ‖Tt l w‖ ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq s _ _
        _ ≤ Y * (b ^ 2 * ‖w‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hcolE s w) (Finset.sum_nonneg fun l _ => by positivity)
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun l _ => by positivity
    by_cases h0 : ‖w‖ = 0
    · rw [h0]; simpa using mul_nonneg (sq_nonneg b) hY0
    · have hpos : 0 < ‖w‖ ^ 2 := by positivity
      have : (‖w‖ ^ 2) ^ 2 ≤ Y * (b ^ 2 * ‖w‖ ^ 2) := by
        calc (‖w‖ ^ 2) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by positivity) hwP 2
          _ ≤ _ := hPY
      nlinarith

end

end ASDExplicitGamma.Scalar
