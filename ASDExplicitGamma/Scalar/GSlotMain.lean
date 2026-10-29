module

public import ASDExplicitGamma.Scalar.GSlotAdjoint

/-! The potential-slot source `G_l(g)` and its transposed row and column bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

section Main

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

local notation "QQ" => originCube 2 nQ

theorem rowKappa_nonneg : 0 ≤ rowKappa QQ m b L := by
  unfold rowKappa
  have := (diagMeshRadius_pos QQ m).le
  positivity

theorem colKappa_nonneg : 0 ≤ colKappa QQ m b L :=
  (rowKappa_nonneg nQ m b L).trans (rowKappa_le_ColKappa QQ m b L)

/-- The Hilbert adjoints of the row maps. -/
theorem gslot_adjoint :
    ∃ A : whiteBasisIndex → GSpace QQ m →L[ℝ] GSpace QQ m,
      (∀ l y z, ⟪A l y, psiZ nQ m z⟫_ℝ = ⟪tZ nQ m b L l z, y⟫_ℝ) ∧
      (∀ (s : Finset whiteBasisIndex) y,
        ∑ l ∈ s, ‖A l y‖ ^ 2 ≤ rowKappa QQ m b L ^ 2 * ‖y‖ ^ 2) ∧
      (∀ (s : Finset whiteBasisIndex) (y : whiteBasisIndex → GSpace QQ m),
        ‖∑ l ∈ s, A l (y l)‖ ^ 2 ≤ colKappa QQ m b L ^ 2 * ∑ l ∈ s, ‖y l‖ ^ 2) := by
  classical
  refine hilbert_transpose (psiZ nQ m) (fun l => tZ nQ m b L l)
    (rowKappa QQ m b L) (colKappa QQ m b L) (rowKappa_nonneg nQ m b L)
    (colKappa_nonneg nQ m b L) ?_ ?_
  · intro s z
    have h := rowElt_column_bound nQ m b L s (rep'' nQ z)
    calc ∑ l ∈ s, ‖tZ nQ m b L l z‖ ^ 2
        = ∑ l ∈ s, tiledPositiveEnergy QQ m (rowElt QQ m b L l (rep'' nQ z)) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          exact phi_norm_sq QQ m _
      _ ≤ _ := h
      _ = _ := by
          change _ = colKappa QQ m b L ^ 2 * ‖PsiL QQ m (gradL2f nQ m (rep'' nQ z))‖ ^ 2
          rw [psi_norm_sq']
  · intro s v
    have h := rowElt_diag_sum_bound QQ m b L (n := s) (fun l => l.1)
      (fun a b' h => Subtype.ext h) (fun l => rep'' nQ (v l.1))
    calc ‖∑ l ∈ s, tZ nQ m b L l (v l)‖ ^ 2
        = tiledPositiveEnergy QQ m (∑ l : s, rowElt QQ m b L l.1 (rep'' nQ (v l.1))) := by
          rw [← phi_norm_sq QQ m, map_sum, ← Finset.sum_coe_sort s]
          rfl
      _ ≤ _ := h
      _ = _ := by
          rw [← Finset.sum_coe_sort s]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          change _ = ‖PsiL QQ m (gradL2f nQ m (rep'' nQ (v l.1)))‖ ^ 2
          rw [psi_norm_sq']

end Main

section Fields

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

local notation "QQ" => originCube 2 nQ

/-- The chosen Hilbert adjoints. -/
def gSlotA : whiteBasisIndex → GSpace QQ m →L[ℝ] GSpace QQ m :=
  Classical.choose (gslot_adjoint nQ m b L)

theorem a_spec :
    (∀ l y z, ⟪gSlotA nQ m b L l y, psiZ nQ m z⟫_ℝ = ⟪tZ nQ m b L l z, y⟫_ℝ) ∧
      (∀ (s : Finset whiteBasisIndex) y,
        ∑ l ∈ s, ‖gSlotA nQ m b L l y‖ ^ 2 ≤ rowKappa QQ m b L ^ 2 * ‖y‖ ^ 2) ∧
      (∀ (s : Finset whiteBasisIndex) (y : whiteBasisIndex → GSpace QQ m),
        ‖∑ l ∈ s, gSlotA nQ m b L l (y l)‖ ^ 2 ≤
          colKappa QQ m b L ^ 2 * ∑ l ∈ s, ‖y l‖ ^ 2) :=
  Classical.choose_spec (gslot_adjoint nQ m b L)

/-- The potential-slot source field `G_l(g)`. -/
def gSlot (l : whiteBasisIndex) (g : TiledL2Field QQ m) : TiledHaarField QQ m :=
  Classical.choose (gSynth (gSlotA nQ m b L l (PsiL QQ m g)))

theorem gSlot_memL2 (l : whiteBasisIndex) (g : TiledL2Field QQ m) :
    MemVectorL2 (openCubeSet QQ) (gSlot nQ m b L l g).1 :=
  (Classical.choose_spec (gSynth (gSlotA nQ m b L l (PsiL QQ m g)))).1

theorem gSlot_spec (l : whiteBasisIndex) (g : TiledL2Field QQ m) (j : GIdx QQ m) :
    (PhiL QQ m (gSlot nQ m b L l g) : GSpace QQ m) j =
      incL j.1.1 j.2.2 ((gSlotA nQ m b L l (PsiL QQ m g) : GSpace QQ m) j) :=
  (Classical.choose_spec (gSynth (gSlotA nQ m b L l (PsiL QQ m g)))).2 j

/-- **Duality (2.3).** `⟨G_l(g), ∇r⟩ = ⟨F_l(r), g⟩` in the tile-averaged pairing. -/
theorem gSlot_dual (l : whiteBasisIndex) (g : TiledL2Field QQ m)
    (z : H10GraphClosedSpace (openCubeSet QQ)) :
    descendantsAverage QQ m (fun R => vectorPairing R (gSlot nQ m b L l g).1
        (rep'' nQ z).toH1Function.grad) =
      descendantsAverage QQ m (fun R => vectorPairing R
        (rowElt QQ m b L l (rep'' nQ z)).1 g.1) := by
  have h1 := phi_psi_inner QQ m (gSlot nQ m b L l g) (gradL2f nQ m (rep'' nQ z))
  have h2 := phi_psi_inner QQ m (rowElt QQ m b L l (rep'' nQ z)) g
  have hdual := (a_spec nQ m b L).1 l (PsiL QQ m g) z
  have h3 := gphi_inner_eq (gSlot nQ m b L l g) (gSlotA nQ m b L l (PsiL QQ m g))
    (gSlot_spec nQ m b L l g) (gradL2f nQ m (rep'' nQ z))
  change ⟪gSlotA nQ m b L l (PsiL QQ m g), PsiL QQ m (gradL2f nQ m (rep'' nQ z))⟫_ℝ =
    ⟪PhiL QQ m (rowElt QQ m b L l (rep'' nQ z)), PsiL QQ m g⟫_ℝ at hdual
  change ⟪PhiL QQ m (gSlot nQ m b L l g), PsiL QQ m (gradL2f nQ m (rep'' nQ z))⟫_ℝ =
    descendantsAverage QQ m (fun R => vectorPairing R (gSlot nQ m b L l g).1
        (rep'' nQ z).toH1Function.grad) at h1
  rw [← h1, ← h2, h3, hdual]

/-- Column bound for the potential slot. -/
theorem gSlot_col (s : Finset whiteBasisIndex) (g : TiledL2Field QQ m) :
    ∑ l ∈ s, tiledPositiveEnergy QQ m (gSlot nQ m b L l g) ≤
      rowKappa QQ m b L ^ 2 * lemmaVTiledWeakEnergy QQ m g.1 := by
  calc ∑ l ∈ s, tiledPositiveEnergy QQ m (gSlot nQ m b L l g)
      = ∑ l ∈ s, ‖PhiL QQ m (gSlot nQ m b L l g)‖ ^ 2 :=
        Finset.sum_congr rfl fun l _ => (phi_norm_sq QQ m _).symm
    _ ≤ ∑ l ∈ s, ‖gSlotA nQ m b L l (PsiL QQ m g)‖ ^ 2 :=
        Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (norm_nonneg _)
          (gphi_norm_le _ _ (gSlot_spec nQ m b L l g)) 2
    _ ≤ rowKappa QQ m b L ^ 2 * ‖PsiL QQ m g‖ ^ 2 := (a_spec nQ m b L).2.1 s _
    _ = _ := by rw [psi_norm_sq]

/-- Row bound for the potential slot. -/
theorem gSlot_row (s : Finset whiteBasisIndex) (g : whiteBasisIndex → TiledL2Field QQ m) :
    tiledPositiveEnergy QQ m (∑ l ∈ s, gSlot nQ m b L l (g l)) ≤
      colKappa QQ m b L ^ 2 * ∑ l ∈ s, lemmaVTiledWeakEnergy QQ m (g l).1 := by
  have hsum := gphi_sum _ s (fun l => gSlot nQ m b L l (g l))
    (fun l => gSlotA nQ m b L l (PsiL QQ m (g l))) (fun l => gSlot_spec nQ m b L l (g l))
  have hn := gphi_norm_le _ _ hsum
  have hrow := (a_spec nQ m b L).2.2 s (fun l => PsiL QQ m (g l))
  calc tiledPositiveEnergy QQ m (∑ l ∈ s, gSlot nQ m b L l (g l))
      = ‖PhiL QQ m (∑ l ∈ s, gSlot nQ m b L l (g l))‖ ^ 2 := (phi_norm_sq QQ m _).symm
    _ ≤ ‖∑ l ∈ s, gSlotA nQ m b L l (PsiL QQ m (g l))‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := hrow
    _ = _ := by
        congr 1
        exact Finset.sum_congr rfl fun l _ => psi_norm_sq QQ m _

end Fields

end

end ASDExplicitGamma.Scalar
