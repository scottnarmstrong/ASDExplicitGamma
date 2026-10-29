module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B81 : ModeBlockData :=
  ⟨⟨98, 100, (4745077665394889647/10000000000000000000000 : ℚ), (245085068909901553/2500000000000000000000 : ℚ)⟩, [
    (98, modeDataJ3M99),
    (99, modeDataJ3M100)], (949015533078977929/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b81 : entryChecks 3 bflatBlockJ3B81.entries = true := by
  simp only [entryChecks,bflatBlockJ3B81,List.all_cons,List.all_nil,
    mode_checked_j3_m99,
    mode_checked_j3_m100,Bool.and_self]
theorem block_mass_checked_j3_b81 : blockMassCheck bflatBlockJ3B81 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
