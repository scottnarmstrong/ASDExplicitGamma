module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B0 : ModeBlockData :=
  ⟨⟨0, 1, (993197356139360021111/5000000000000000000000 : ℚ), (127147377381404886461/5000000000000000000000 : ℚ)⟩, [
    (0, modeDataJ1M1)], (1986394712278720042221/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b0 : entryChecks 1 bflatBlockJ1B0.entries = true := by
  simp only [entryChecks,bflatBlockJ1B0,List.all_cons,List.all_nil,
    mode_checked_j1_m1,Bool.and_self]
theorem block_mass_checked_j1_b0 : blockMassCheck bflatBlockJ1B0 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
