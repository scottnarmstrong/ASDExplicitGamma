module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B39 : ModeBlockData :=
  ⟨⟨39, 40, (12516961842806059187/5000000000000000000000 : ℚ), (19664600177251869/5000000000000000000000 : ℚ)⟩, [
    (39, modeDataJ5M40)], (25033923685612118373/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b39 : entryChecks 5 bflatBlockJ5B39.entries = true := by
  simp only [entryChecks,bflatBlockJ5B39,List.all_cons,List.all_nil,
    mode_checked_j5_m40,Bool.and_self]
theorem block_mass_checked_j5_b39 : blockMassCheck bflatBlockJ5B39 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
