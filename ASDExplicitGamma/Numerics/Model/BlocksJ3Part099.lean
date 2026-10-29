module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B99 : ModeBlockData :=
  ⟨⟨151, 155, (64402935387425413/625000000000000000000 : ℚ), (181986872379984731/2500000000000000000000 : ℚ)⟩, [
    (151, modeDataJ3M152),
    (152, modeDataJ3M153),
    (153, modeDataJ3M154),
    (154, modeDataJ3M155)], (257611741549701651/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b99 : entryChecks 3 bflatBlockJ3B99.entries = true := by
  simp only [entryChecks,bflatBlockJ3B99,List.all_cons,List.all_nil,
    mode_checked_j3_m152,
    mode_checked_j3_m153,
    mode_checked_j3_m154,
    mode_checked_j3_m155,Bool.and_self]
theorem block_mass_checked_j3_b99 : blockMassCheck bflatBlockJ3B99 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
