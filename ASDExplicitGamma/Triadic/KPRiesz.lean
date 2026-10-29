module

public import ASDExplicitGamma.Triadic.TriadicDualNorms
public import ASDExplicitGamma.Triadic.PoincareTorus
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Constant-one triadic duality, equal-norm Riesz representation, and mixed-mode Bessel.
The convergence hypotheses are exactly those of TR-KP-RIESZ's pinned source statement. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory

noncomputable section

/-- Source weak/positive duality on a cube, with the explicit limiting pairing. -/
theorem weak_positive_duality_of_weight {d : ℕ} (Q : TriadicCube d) {q : ℝ}
    (hq : 1 < q) {f h : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun k => q^(k+1)*energy Q (cubeIncrement Q (k+1) h)))
    (hlim : Filter.Tendsto (fun N => pairing Q (cubeProjection Q N f) (cubeProjection Q N h))
      Filter.atTop (nhds (pairing Q f h))) :
    |pairing Q f h| ≤ Real.sqrt (dualEnergy Q q f)*Real.sqrt (primalEnergy Q q h) :=
  abs_pairing_le_dual_primal_of_pairing_limit Q hq hf hh hs hlim

/-- Source exponent form of constant-one weak/positive duality. -/
theorem weak_positive_duality {d : ℕ} (Q : TriadicCube d) (s : ℝ) (hs : 0 < s) :
    let q := (3:ℝ)^(2*s)
    ∀ (f h : Vec d → ℝ),
      MemLp f 2 (normalizedCubeMeasure Q) → MemLp h 2 (normalizedCubeMeasure Q) →
      Summable (fun k => q^(k+1)*energy Q (cubeIncrement Q (k+1) h)) →
      Filter.Tendsto (fun N => pairing Q (cubeProjection Q N f) (cubeProjection Q N h))
        Filter.atTop (nhds (pairing Q f h)) →
      |pairing Q f h| ≤ Real.sqrt (dualEnergy Q q f)*Real.sqrt (primalEnergy Q q h) := by
  intro q f h hf hh hsum hlim
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (mul_pos (by norm_num) hs)
  exact weak_positive_duality_of_weight Q hq hf hh hsum hlim

/-- Every bounded functional on a real Hilbert energy space has a unique
representing vector of exactly the same norm. -/
theorem energy_riesz_representation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (L : E →L[ℝ] ℝ) :
    ∃! y : E, (∀ x, L x = inner ℝ y x) ∧ ‖y‖ = ‖L‖ := by
  let y := (InnerProductSpace.toDual ℝ E).symm L
  have hy : ∀ x, L x = inner ℝ y x := fun x =>
    (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := x) (y := L)).symm
  have hn : ‖y‖ = ‖L‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map L
  refine ⟨y, ⟨hy, hn⟩, ?_⟩
  intro z hz
  apply (InnerProductSpace.toDual ℝ E).injective
  have hL : InnerProductSpace.toDual ℝ E z = L := by
    ext x
    exact (hz.1 x).symm
  rw [hL]
  exact ((InnerProductSpace.toDual ℝ E).apply_symm_apply L).symm

/-- Mixed-sine/cosine Bessel inequality on every physical box, including
summability of the actual coefficient-square series. -/
theorem mixed_box_bessel {d : ℕ} (a : Fin d → ℝ) {r : ℝ} (hr : 0 < r)
    (O : Finset (Fin d)) {φ : Vec d → ℝ} (hφ : MemLp φ 2 (Torus.boxMeasure a r)) :
    Summable (fun n : Fin d → ℤ =>
      (∫ x, Torus.boxMode a r O n x*φ x ∂Torus.boxMeasure a r)^2) ∧
    (∑' n : Fin d → ℤ, (∫ x, Torus.boxMode a r O n x*φ x ∂Torus.boxMeasure a r)^2) ≤
      ∫ x, φ x^2 ∂Torus.boxMeasure a r :=
  ⟨Torus.summable_sq_boxCoeff a hr O hφ, Torus.tsum_sq_boxCoeff_le a hr O hφ⟩

end

end ASDExplicitGamma.Triadic
