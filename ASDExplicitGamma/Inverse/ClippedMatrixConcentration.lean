module

public import ASDExplicitGamma.Inverse.ClippedMatrixHoeffding
public import ASDExplicitGamma.Inverse.ClippedMatrixEntryNorm

/-! Colored matrix Hoeffding for the actual inverse application R_i=I.
The deterministic sensitivity multiplier is not included in the centered sum. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.Norms.Elementwise

/-- The matrix entrywise mean form of the source bound for identity conjugators.
Only independence within fixed colors is used; no cluster mask is present. -/
theorem clipped_colored_matrix_Lp {Ω I K n : Type*} [MeasurableSpace Ω]
    [Fintype I] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : I → Ω → Matrix n n ℝ) (color : I → K)
    (hind : ∀ k, iIndepFun (fun i : {i // color i=k} => Y i.1) μ)
    (hm : ∀ i, Measurable (Y i)) (G : ℝ) (hG : 0 ≤ G)
    (hb : ∀ i a b, ∀ᵐ ω ∂μ, |Y i ω a b| ≤ G) (w : I → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    let F := fun ω a b => ∑ i, w i*(Y i ω a b-∫ ζ, Y i ζ a b ∂μ)
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (F ω)‖) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (2*(Fintype.card n:ℝ)^2*G*Real.sqrt p*
        Real.sqrt (∑ i, (w i)^2)*Real.sqrt (Fintype.card K:ℝ)) := by
  let F : Ω → Matrix n n ℝ := fun ω a b => ∑ i, w i*(Y i ω a b-∫ ζ, Y i ζ a b ∂μ)
  let B := 2*G*Real.sqrt p*Real.sqrt (∑ i, (w i)^2)*Real.sqrt (Fintype.card K:ℝ)
  have hYm (i : I) (a b : n) : Measurable (fun ω => Y i ω a b) :=
    (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hm i))
  have hF (a b : n) : Measurable (fun ω => F ω a b) :=
    Finset.measurable_sum _ (fun i _ => ((hYm i a b).sub_const _).const_mul _)
  have hi (a b : n) (k : K) : iIndepFun (fun i : {i // color i=k} => fun ω => Y i.1 ω a b) μ :=
    (hind k).comp (fun _ A => A a b)
      (fun _ => (measurable_pi_apply b).comp (measurable_pi_apply a))
  have hs (a b : n) : eLpNorm (fun ω => F ω a b) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal B :=
    clipped_colored_entry_Lp μ (fun i ω => Y i ω a b) color (hi a b)
      (fun i => hYm i a b) G hG (fun i => hb i a b) w p hp
  have hh := clipped_matrix_Lp_of_entries μ F hF (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr hp) B (by dsimp only [B]; positivity) hs
  apply hh.trans_eq
  congr 1
  dsimp only [B]
  ring

end ASDExplicitGamma.Inverse
