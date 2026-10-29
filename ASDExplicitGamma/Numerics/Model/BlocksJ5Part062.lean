module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B62 : ModeBlockData :=
  ⟨⟨62, 63, (24760038937997205831/10000000000000000000000 : ℚ), (2440972154891517/625000000000000000000 : ℚ)⟩, [
    (62, modeDataJ5M63)], (2476003893799720583/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b62 : entryChecks 5 bflatBlockJ5B62.entries = true := by
  simp only [entryChecks,bflatBlockJ5B62,List.all_cons,List.all_nil,
    mode_checked_j5_m63,Bool.and_self]
theorem block_mass_checked_j5_b62 : blockMassCheck bflatBlockJ5B62 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
