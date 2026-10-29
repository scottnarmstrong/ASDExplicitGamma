module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B8 : ModeBlockData :=
  ⟨⟨8, 9, (52189446232445792843/10000000000000000000000 : ℚ), (81712240956571301/16000000000000000000 : ℚ)⟩, [
    (8, modeDataJ0M9)], (26094723116222896421/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b8 : entryChecks 0 bflatBlockJ0B8.entries = true := by
  simp only [entryChecks,bflatBlockJ0B8,List.all_cons,List.all_nil,
    mode_checked_j0_m9,Bool.and_self]
theorem block_mass_checked_j0_b8 : blockMassCheck bflatBlockJ0B8 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
