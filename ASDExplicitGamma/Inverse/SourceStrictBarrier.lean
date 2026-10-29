module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Linarith

/-! A continuous scalar path cannot cross a strict barrier when its
boundary derivatives point inward. No derivative at time zero is required. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Set Filter
open scoped Topology

/-- Strict barrier comparison using derivatives only at positive-time
boundary contacts. Continuity alone suffices at the initial time. -/
theorem source_strict_barrier
    (f B : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) 1))
    (hB : ContinuousOn B (Icc (0:ℝ) 1)) (hstart : f 0 < B 0)
    (hboundary : ∀ x ∈ Ioo (0:ℝ) 1, f x=B x →
      ∃ d, HasDerivAt (fun t => f t-B t) d x ∧ d<0) :
    ∀ x ∈ Icc (0:ℝ) 1, f x ≤ B x := by
  let s := {x | f x ≤ B x} ∩ Icc (0:ℝ) 1
  have hpair : ContinuousOn (fun x => (f x,B x)) (Icc (0:ℝ) 1) := hf.prodMk hB
  have hs : IsClosed s := by
    dsimp only [s]
    rw [inter_comm]
    exact hpair.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  have hsub : Icc (0:ℝ) 1 ⊆ {x | f x ≤ B x} := by
    apply hs.Icc_subset_of_forall_exists_gt hstart.le
    rintro x ⟨hfx,hx⟩ y hy
    change f x ≤ B x at hfx
    rcases hfx.lt_or_eq with hlt | heq
    · have hevent : ∀ᶠ z in 𝓝[Icc (0:ℝ) 1] x, f z < B z :=
        hpair x (Ico_subset_Icc_self hx) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hlt)
      have hevent' : ∀ᶠ z in 𝓝[>] x, f z < B z :=
        nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) hevent
      exact nonempty_of_mem (inter_mem (hevent'.mono fun z hz => hz.le) (Ioc_mem_nhdsGT hy))
    · have hx0 : 0 < x := by
        rcases hx.1.eq_or_lt with he | he
        · subst x
          exact (hstart.ne heq).elim
        · exact he
      obtain ⟨d,hd,hd0⟩ := hboundary x ⟨hx0,hx.2⟩ heq
      obtain ⟨z,hz,hzy⟩ := ((hd.hasDerivWithinAt (s := Ici x)).liminf_right_slope_le hd0).and_eventually (Ioc_mem_nhdsGT hy) |>.exists
      have hgx : f x-B x=0 := sub_eq_zero.mpr heq
      rw [slope_def_field,hgx,sub_zero] at hz
      have hz0 : f z-B z<0 := by
        have hh := (div_lt_iff₀ (sub_pos.mpr hzy.1)).mp hz
        simpa only [zero_mul] using hh
      exact ⟨z,(sub_neg.mp hz0).le,hzy⟩
  exact fun x hx => hsub hx

end ASDExplicitGamma.Inverse
