module

public import ASDExplicitGamma.Native.ParentBoundaryBrokenTrace

/-! Fine-cell root histories control shifted parent inverse maxima with
no spurious loss from the comparison depth. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Every deeper parent descendant belongs to a cell of the comparison
partition, with the remaining depth unchanged. -/
theorem parent_boundary_descendant_split (Q R : TriadicCube 2) (depth j : ℕ)
    (hR : R ∈ descendantsAtDepth Q (depth+j)) :
    ∃ U ∈ descendantsAtDepth Q depth,R ∈ descendantsAtDepth U j := by
  induction j generalizing R with
  | zero =>
    refine ⟨R,?_,?_⟩
    · simpa only [Nat.add_zero] using hR
    · simp only [descendantsAtDepth_zero,Finset.mem_singleton]
  | succ j ih =>
    have hR' : R ∈ descendantsAtDepth Q ((depth+j)+1) := by simpa only [Nat.add_assoc] using hR
    obtain ⟨S,hS,hRS⟩ := mem_descendantsAtDepth_succ_iff.mp hR'
    obtain ⟨U,hU,hSU⟩ := ih S hS
    exact ⟨U,hU,mem_descendantsAtDepth_succ_iff.mpr ⟨S,hSU,hRS⟩⟩

/-- A common bound for the COMPLETE inverse histories of the comparison
cells controls each shifted discounted inverse maximum with constant one. -/
theorem parent_boundary_broken_inverse_discount (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : ℝ) (hP : ∀ U ∈ descendantsAtDepth Q depth,
      lemmaVInverseHistory U a ((3:ℝ)^(1/4:ℝ))≤P) (j : ℕ) :
    inverseHistoryDiscount^j*lemmaVInverseDepthMax Q a (depth+j)≤P := by
  classical
  let S := descendantsAtDepth Q (depth+j)
  let f := fun R : TriadicCube 2 => Book.Ch02.matrixNorm
    (sigmaStarInvCoarse (openCubeSet R) a)
  have hfinite : (f '' (S : Set (TriadicCube 2))).Finite := S.finite_toSet.image f
  have hne : (f '' (S : Set (TriadicCube 2))).Nonempty :=
    (descendantsAtDepth_nonempty Q (depth+j)).to_set.image f
  obtain ⟨R,hR,he⟩ := hne.csSup_mem hfinite
  change inverseHistoryDiscount^j*sSup (f '' (S : Set (TriadicCube 2)))≤P
  rw [←he]
  obtain ⟨U,hU,hRU⟩ := parent_boundary_descendant_split Q R depth j hR
  have hlocal : f R≤lemmaVInverseDepthMax U a j := by
    unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R,hRU,rfl⟩
  have hEllU := hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hd := actual_inverse_depth_discount_bound U a hEllU 1 (by norm_num) j
  simp only [one_mul] at hd
  exact ((mul_le_mul_of_nonneg_left hlocal (pow_nonneg inverse_history_discount_range.1.le j)).trans hd).trans (hP U hU)

/-- Shifted complete weak trace weights remain genuinely summable. -/
theorem parent_boundary_broken_weak_trace_summable (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => inverseHistoryDiscount^j*
      descendantsAverage Q (depth+j) (fun U => traceDefect (openCubeSet U) a 1)) := by
  let alpha := inverseHistoryDiscount
  let f := fun j => descendantsAverage Q j (fun U => traceDefect (openCubeSet U) a 1)
  have hs : Summable (fun j : ℕ => alpha^j*f j) := old_signed_trace_depth_series_summable Q a hEll
  have ht : Summable (fun j : ℕ => alpha^(depth+j)*f (depth+j)) :=
    hs.comp_injective (show Function.Injective (fun j : ℕ => depth+j) from fun _ _ hh => Nat.add_left_cancel hh)
  have hn : alpha^depth≠0 := pow_ne_zero _ inverse_history_discount_range.1.ne'
  apply (ht.mul_left ((alpha^depth)⁻¹)).congr
  intro j
  calc
    _ = (alpha^depth)⁻¹*alpha^depth*(alpha^j*f (depth+j)) := by rw [pow_add]; ring
    _ = _ := by rw [inv_mul_cancel₀ hn,one_mul]

end
end ASDExplicitGamma.Native
