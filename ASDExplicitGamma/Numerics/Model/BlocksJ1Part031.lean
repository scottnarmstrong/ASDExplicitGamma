module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B31 : ModeBlockData :=
  ⟨⟨31, 32, (4075703942324655039/10000000000000000000000 : ℚ), (1003795157370970429/2500000000000000000000 : ℚ)⟩, [
    (31, modeDataJ1M32)], (2037851971162327519/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b31 : entryChecks 1 bflatBlockJ1B31.entries = true := by
  simp only [entryChecks,bflatBlockJ1B31,List.all_cons,List.all_nil,
    mode_checked_j1_m32,Bool.and_self]
theorem block_mass_checked_j1_b31 : blockMassCheck bflatBlockJ1B31 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
