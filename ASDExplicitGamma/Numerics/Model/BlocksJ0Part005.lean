module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B5 : ModeBlockData :=
  ⟨⟨5, 6, (31446581526561622387/2500000000000000000000 : ℚ), (118348351779274202343/10000000000000000000000 : ℚ)⟩, [
    (5, modeDataJ0M6)], (125786326106246489547/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b5 : entryChecks 0 bflatBlockJ0B5.entries = true := by
  simp only [entryChecks,bflatBlockJ0B5,List.all_cons,List.all_nil,
    mode_checked_j0_m6,Bool.and_self]
theorem block_mass_checked_j0_b5 : blockMassCheck bflatBlockJ0B5 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
