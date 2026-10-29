module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B24 : ModeBlockData :=
  ⟨⟨24, 25, (6824589406970695297/10000000000000000000000 : ℚ), (6643186845656938783/10000000000000000000000 : ℚ)⟩, [
    (24, modeDataJ1M25)], (53317104741958557/78125000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b24 : entryChecks 1 bflatBlockJ1B24.entries = true := by
  simp only [entryChecks,bflatBlockJ1B24,List.all_cons,List.all_nil,
    mode_checked_j1_m25,Bool.and_self]
theorem block_mass_checked_j1_b24 : blockMassCheck bflatBlockJ1B24 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
