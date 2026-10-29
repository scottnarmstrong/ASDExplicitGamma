module

public import ASDExplicitGamma.Inverse.SourceStrictBarrier
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Uniform twentieth-moment root bounds from a strict scalar barrier.
The moment derivative is used only at positive contact values. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Set

/-- A conditional p20 drift estimate below `X`, together with the strict
budget `a+c<X`, proves the uniform cap `X`. This discharges a bootstrap
premise rather than assuming the path stays in its comparison region. -/
theorem source_p20_moment_strict_barrier
    (f df : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hf0 : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ f t)
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (df t) t)
    (a c X : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hbudget : a+c<X)
    (hstart : f 0^((20:ℝ)⁻¹) ≤ a)
    (hdrift : ∀ t ∈ Ioo (0:ℝ) 1, f t^((20:ℝ)⁻¹) ≤ X →
      df t ≤ 20*f t^((19:ℝ)/20)*c) :
    ∀ t ∈ Icc (0:ℝ) 1, f t^((20:ℝ)⁻¹) ≤ X := by
  let δ := (X-a-c)/3
  let B := fun t : ℝ => a+δ+(c+δ)*t
  have hδ : 0 < δ := by dsimp [δ]; linarith only [hbudget]
  have hcd : 0 ≤ c+δ := add_nonneg hc hδ.le
  have hroot : ContinuousOn (fun t => f t^((20:ℝ)⁻¹)) (Icc (0:ℝ) 1) :=
    hf.rpow_const (fun _ _ => Or.inr (by norm_num))
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hBcap (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : B t ≤ X := by
    have hh := mul_le_mul_of_nonneg_left ht.2 hcd
    dsimp only [B,δ] at ⊢ hh
    linarith only [hh,hbudget]
  have hstart' : f 0^((20:ℝ)⁻¹)<B 0 := by
    dsimp only [B]
    linarith only [hstart,hδ]
  have hall := source_strict_barrier (fun t => f t^((20:ℝ)⁻¹)) B hroot hB.continuousOn hstart' ?_
  · intro t ht
    exact (hall t ht).trans (hBcap t ht)
  · intro t ht heq
    have hBpos : 0 < B t := by
      dsimp only [B]
      exact add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos ha hδ) (mul_nonneg hcd ht.1.le)
    have hne : f t≠0 := by
      intro hz
      rw [hz,Real.zero_rpow (by norm_num : (20:ℝ)⁻¹≠0)] at heq
      linarith only [heq,hBpos]
    have hpos : 0 < f t := lt_of_le_of_ne (hf0 t ⟨ht.1.le,ht.2.le⟩) (Ne.symm hne)
    have hcap : f t^((20:ℝ)⁻¹) ≤ X := heq.le.trans (hBcap t ⟨ht.1.le,ht.2.le⟩)
    let k := (20:ℝ)⁻¹*f t^((20:ℝ)⁻¹-1)
    have hk : 0 ≤ k := by dsimp [k]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg hpos.le _)
    have hcancel : k*(20*f t^((19:ℝ)/20))=1 := by
      dsimp only [k]
      calc
        _ = f t^((20:ℝ)⁻¹-1)*f t^((19:ℝ)/20) := by ring
        _ = f t^(((20:ℝ)⁻¹-1)+(19:ℝ)/20) := (Real.rpow_add hpos _ _).symm
        _ = 1 := by norm_num
    have hderiv : k*df t ≤ c := by
      have hh := mul_le_mul_of_nonneg_left (hdrift t ht hcap) hk
      calc
        _ ≤ k*(20*f t^((19:ℝ)/20)*c) := hh
        _ = c := by rw [←mul_assoc,hcancel,one_mul]
    have hdroot : HasDerivAt (fun s => f s^((20:ℝ)⁻¹)) (k*df t) t := by
      convert (hdf t ht).rpow_const (p := (20:ℝ)⁻¹) (Or.inl hne) using 1
      dsimp [k]
      ring
    have hdB : HasDerivAt B (c+δ) t := by
      simpa only [B,mul_one,id_eq] using ((hasDerivAt_id t).const_mul (c+δ)).const_add (a+δ)
    refine ⟨k*df t-(c+δ),hdroot.sub hdB,?_⟩
    linarith only [hderiv,hδ]

end ASDExplicitGamma.Inverse
