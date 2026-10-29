module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B13 : ModeBlockData :=
  ⟨⟨13, 14, (13184051740786271899/625000000000000000000 : ℚ), (305462355290843381/1000000000000000000000 : ℚ)⟩, [
    (13, modeDataJ3M14)], (210944827852580350383/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b13 : entryChecks 3 bflatBlockJ3B13.entries = true := by
  simp only [entryChecks,bflatBlockJ3B13,List.all_cons,List.all_nil,
    mode_checked_j3_m14,Bool.and_self]
theorem block_mass_checked_j3_b13 : blockMassCheck bflatBlockJ3B13 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
