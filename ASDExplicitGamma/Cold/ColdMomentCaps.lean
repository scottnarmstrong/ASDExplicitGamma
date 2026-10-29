module

public import ASDExplicitGamma.Cold.ColdMomentUpdate
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Cold moment-cap constants and valid triangular updates -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The source transported centered twentieth-moment cap at depth d. -/
def coldCenteredMomentCap (M : ℝ) (d : ℕ) : ℝ :=
  if d=0 then M else min M (2*Real.sqrt 19*(3:ℝ)^(-(d:ℝ))*M)

/-- Exact conversion from the square population `N=9^d` to the source depth decay. -/
theorem cold_square_population_factor (d : ℕ) :
    2*Real.sqrt 19/Real.sqrt ((9:ℝ)^d) = 2*Real.sqrt 19*(3:ℝ)^(-(d:ℝ)) := by
  have he : Real.sqrt ((9:ℝ)^d) = (3:ℝ)^d := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [pow_right_comm]
    norm_num
  rw [he,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),Real.rpow_natCast]
  ring

/-- CO-COLD-MOMENT-CAPS update at positive depth, using the actual finite child traces.
The inputs are the source child moment/mean caps, within-colour independence and
pathwise trace subadditivity; the sharp cap is a conclusion. -/
theorem cold_moment_cap_update {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] (color : ι → Fin 4)
    {X : ι → Ω → ℝ} {T : Ω → ℝ} {M D : ℝ} {d : ℕ}
    (hd : 0 < d) (hcard : Fintype.card ι = 9^d)
    (hX : ∀ i, MemLp (X i) 20 ℙ) (hn : ∀ i, ∀ᵐ ω ∂ℙ, 0 ≤ X i ω)
    (hi : ∀ c, ProbabilityTheory.iIndepFun (fun i : {i // color i = c} => X i.val) ℙ)
    (hM : 0 ≤ M) (hcap : ∀ i, lpNorm (X i) 20 ℙ ≤ M)
    (hmean : (∑ i, ∫ ω, X i ω ∂ℙ)/(Fintype.card ι:ℝ) ≤ D)
    (hT : ∀ᵐ ω ∂ℙ, 0 ≤ T ω)
    (hsub : ∀ᵐ ω ∂ℙ, T ω ≤ (∑ i, X i ω)/(Fintype.card ι:ℝ)) :
    lpNorm T 20 ℙ ≤ min M (D+coldCenteredMomentCap M d) := by
  have h := cold_moment_update color hX hn hi hM hcap hmean hT hsub
  rw [hcard,Nat.cast_pow,Nat.cast_ofNat,cold_square_population_factor] at h
  simpa only [coldCenteredMomentCap,ite_eq_right (Nat.ne_of_gt hd)] using h

/-- Every transported centered cap is nonnegative. -/
theorem coldCenteredMomentCap_nonneg {M : ℝ} (hM : 0 ≤ M) (d : ℕ) :
    0 ≤ coldCenteredMomentCap M d := by
  unfold coldCenteredMomentCap
  split_ifs
  · exact hM
  · exact le_min hM (by positivity)

end ASDExplicitGamma.Cold
