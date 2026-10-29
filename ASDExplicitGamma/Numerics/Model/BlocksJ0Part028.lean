module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B28 : ModeBlockData :=
  ⟨⟨28, 29, (4837343525347768977/10000000000000000000000 : ℚ), (603523371450710941/1250000000000000000000 : ℚ)⟩, [
    (28, modeDataJ0M29)], (302333970334235561/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b28 : entryChecks 0 bflatBlockJ0B28.entries = true := by
  simp only [entryChecks,bflatBlockJ0B28,List.all_cons,List.all_nil,
    mode_checked_j0_m29,Bool.and_self]
theorem block_mass_checked_j0_b28 : blockMassCheck bflatBlockJ0B28 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
