module

public import ASDExplicitGamma.Native.HeatConfiguredSourceRows
public import ASDExplicitGamma.Native.HeatCooperativeSystem

/-! The exact physical-moment right side behind each configured matrix row. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- The three stored matrix entries are exactly the source producer row in
physical moment units, including the degree-dependent forcing scale. -/
theorem native_configured_source_rhs_eq (j : Fin 153) (i : Fin 21) (hi : i.val ≠ 0)
    (current previous : ℝ) :
    let c := nativeIndividualRow (nativeConfiguredSystem j).gap i.val (nativeOld (nativeConfiguredSystem j).gap)
    ((nativeConfiguredSystem j).system.diag.getD i.val 0:ℝ)*current +
      ((nativeConfiguredSystem j).system.subdiag.getD i.val 0:ℝ)*
        ((3/50:ℝ)*((nativeConfiguredSystem j).system.z:ℝ))*previous +
      ((nativeConfiguredSystem j).system.force.getD i.val 0:ℝ)*nativeConfiguredMomentScale j i =
    (c.2.1:ℝ)*current + (3/50:ℝ)*(c.1:ℝ)*previous + (3/50:ℝ)^i.val*(c.2.2:ℝ) := by
  dsimp only
  obtain ⟨hd,hs,hf⟩ := native_configured_individual_row_unscale j i hi
  have hsR : ((nativeConfiguredSystem j).system.subdiag.getD i.val 0:ℝ)*
      ((nativeConfiguredSystem j).system.z:ℝ) =
      ((nativeIndividualRow (nativeConfiguredSystem j).gap i.val (nativeOld (nativeConfiguredSystem j).gap)).1:ℝ) := by exact_mod_cast hs
  have hfR : ((nativeConfiguredSystem j).system.force.getD i.val 0:ℝ)*
      ((nativeConfiguredSystem j).system.z:ℝ)^i.val =
      ((nativeIndividualRow (nativeConfiguredSystem j).gap i.val (nativeOld (nativeConfiguredSystem j).gap)).2.2:ℝ) := by exact_mod_cast hf
  rw [hd]
  unfold nativeConfiguredMomentScale
  calc
    _ = ((nativeIndividualRow (nativeConfiguredSystem j).gap i.val (nativeOld (nativeConfiguredSystem j).gap)).2.1:ℝ)*current + (3/50:ℝ)*
        (((nativeConfiguredSystem j).system.subdiag.getD i.val 0:ℝ)*
          ((nativeConfiguredSystem j).system.z:ℝ))*previous +
        (3/50:ℝ)^i.val*(((nativeConfiguredSystem j).system.force.getD i.val 0:ℝ)*
          ((nativeConfiguredSystem j).system.z:ℝ)^i.val) := by ring
    _ = _ := by rw [hsR,hfR]

/-- Source-to-matrix interface: once the physical generator is bounded
by its degree-specific individual producer row, its exact configured row
follows with no extra coefficient comparison hypotheses. -/
theorem native_configured_row_of_individual_source (j : Fin 153) (i : Fin 21)
    (hi : i.val ≠ 0) (current previous generator : ℝ)
    (hsource : let c := nativeIndividualRow (nativeConfiguredSystem j).gap i.val (nativeOld (nativeConfiguredSystem j).gap)
      generator ≤ (c.2.1:ℝ)*current + (3/50:ℝ)*(c.1:ℝ)*previous + (3/50:ℝ)^i.val*(c.2.2:ℝ)) :
    generator ≤ ((nativeConfiguredSystem j).system.diag.getD i.val 0:ℝ)*current +
      ((nativeConfiguredSystem j).system.subdiag.getD i.val 0:ℝ)*
        ((3/50:ℝ)*((nativeConfiguredSystem j).system.z:ℝ))*previous +
      ((nativeConfiguredSystem j).system.force.getD i.val 0:ℝ)*nativeConfiguredMomentScale j i := by
  rw [native_configured_source_rhs_eq j i hi]
  exact hsource

end
end ASDExplicitGamma.Native
