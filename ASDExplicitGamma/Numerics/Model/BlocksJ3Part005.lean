module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B5 : ModeBlockData :=
  ⟨⟨5, 6, (223957202612692710397/10000000000000000000000 : ℚ), (634666258554134647/2000000000000000000000 : ℚ)⟩, [
    (5, modeDataJ3M6)], (55989300653173177599/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b5 : entryChecks 3 bflatBlockJ3B5.entries = true := by
  simp only [entryChecks,bflatBlockJ3B5,List.all_cons,List.all_nil,
    mode_checked_j3_m6,Bool.and_self]
theorem block_mass_checked_j3_b5 : blockMassCheck bflatBlockJ3B5 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
