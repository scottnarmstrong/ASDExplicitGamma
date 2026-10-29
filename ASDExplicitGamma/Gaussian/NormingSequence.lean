module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Bases

/-! # A countable norming sequence for a separable real normed space -/

@[expose] public section

open TopologicalSpace Set

namespace ASDExplicitGamma.Gaussian

section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]

/-- Hahn–Banach norming functionals at a fixed dense sequence. -/
noncomputable def normingSequence (n : ℕ) : E →L[ℝ] ℝ :=
  Classical.choose (exists_dual_vector'' ℝ (denseSeq E n))

theorem norm_normingSequence_le (n : ℕ) : ‖normingSequence E n‖ ≤ 1 :=
  (Classical.choose_spec (exists_dual_vector'' ℝ (denseSeq E n))).1

theorem normingSequence_denseSeq (n : ℕ) : normingSequence E n (denseSeq E n) = ‖denseSeq E n‖ :=
  (Classical.choose_spec (exists_dual_vector'' ℝ (denseSeq E n))).2

theorem normingSequence_apply_le (n : ℕ) (x : E) : normingSequence E n x ≤ ‖x‖ :=
  (le_abs_self _).trans ((normingSequence E n).le_opNorm x |>.trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (norm_normingSequence_le E n) (norm_nonneg x)))

/-- The norm is an actual countable supremum of linear Gaussian observations. -/
theorem norm_eq_iSup_normingSequence (x : E) : ‖x‖ = ⨆ n, normingSequence E n x := by
  have hb : BddAbove (range fun n => normingSequence E n x) :=
    ⟨‖x‖, fun y ⟨n, hn⟩ => hn ▸ normingSequence_apply_le E n x⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := (denseRange_denseSeq E).exists_dist_lt x (half_pos hε)
    let z := denseSeq E n
    have hdist : ‖z - x‖ < ε / 2 := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact hn
    have hfun : normingSequence E n z - normingSequence E n x ≤ ‖z - x‖ := by
      rw [← map_sub]
      exact normingSequence_apply_le E n (z - x)
    have hnz : normingSequence E n z = ‖z‖ := normingSequence_denseSeq E n
    have hnorm : ‖x‖ - ‖z‖ ≤ ‖z - x‖ := by
      simpa only [norm_sub_rev] using norm_sub_norm_le x z
    have hs := le_ciSup hb n
    rw [hnz] at hfun
    linarith only [hfun, hnorm, hs, hdist]
  · exact ciSup_le (normingSequence_apply_le E · x)

end
end ASDExplicitGamma.Gaussian
