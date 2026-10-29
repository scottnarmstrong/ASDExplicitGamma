module

public import ASDExplicitGamma.Variational.ProjectedSource
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! The actual complete inverse-history maximum over the source-cell tiling. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Variational
noncomputable section

def pureFluxSourceTileHistory (Q : TriadicCube 2) (m : ℕ) (a : CoeffField 2) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q m)
    (fun U => lemmaVInverseHistory U a ((3:ℝ)^(1/4:ℝ)))

theorem pureFlux_source_tile_history_member_le (Q : TriadicCube 2) (m : ℕ)
    (a : CoeffField 2) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
    lemmaVInverseHistory U a ((3:ℝ)^(1/4:ℝ)) ≤ pureFluxSourceTileHistory Q m a := by
  unfold pureFluxSourceTileHistory Book.Ch02.finsetSupReal
  exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨U, hU, rfl⟩

theorem pureFlux_source_tile_history_nonneg (Q : TriadicCube 2) (m : ℕ) (a : CoeffField 2) :
    0 ≤ pureFluxSourceTileHistory Q m a := by
  obtain ⟨U, hU⟩ := descendantsAtDepth_nonempty Q m
  exact (lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))).trans
    (pureFlux_source_tile_history_member_le Q m a U hU)

theorem pureFlux_source_tile_history_le (Q : TriadicCube 2) (m : ℕ) (a : CoeffField 2)
    (B : ℝ) (hB : ∀ U ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory U a ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    pureFluxSourceTileHistory Q m a ≤ B := by
  exact Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q m) hB

end
end ASDExplicitGamma.Inverse
