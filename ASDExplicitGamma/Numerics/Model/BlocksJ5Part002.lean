module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B2 : ModeBlockData :=
  ⟨⟨2, 3, (12609702884696547397/5000000000000000000000 : ℚ), (3951415592380671/1000000000000000000000 : ℚ)⟩, [
    (2, modeDataJ5M3)], (25219405769393094793/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b2 : entryChecks 5 bflatBlockJ5B2.entries = true := by
  simp only [entryChecks,bflatBlockJ5B2,List.all_cons,List.all_nil,
    mode_checked_j5_m3,Bool.and_self]
theorem block_mass_checked_j5_b2 : blockMassCheck bflatBlockJ5B2 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
