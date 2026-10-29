module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B24 : ModeBlockData :=
  ⟨⟨24, 25, (179383714323531126523/10000000000000000000000 : ℚ), (1379902699953507157/5000000000000000000000 : ℚ)⟩, [
    (24, modeDataJ3M25)], (89691857161765563261/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b24 : entryChecks 3 bflatBlockJ3B24.entries = true := by
  simp only [entryChecks,bflatBlockJ3B24,List.all_cons,List.all_nil,
    mode_checked_j3_m25,Bool.and_self]
theorem block_mass_checked_j3_b24 : blockMassCheck bflatBlockJ3B24 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
