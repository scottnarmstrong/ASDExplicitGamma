module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B17 : ModeBlockData :=
  ⟨⟨17, 18, (6295645871720548791/2500000000000000000000 : ℚ), (9869365353290713/2500000000000000000000 : ℚ)⟩, [
    (17, modeDataJ5M18)], (25182583486882195163/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b17 : entryChecks 5 bflatBlockJ5B17.entries = true := by
  simp only [entryChecks,bflatBlockJ5B17,List.all_cons,List.all_nil,
    mode_checked_j5_m18,Bool.and_self]
theorem block_mass_checked_j5_b17 : blockMassCheck bflatBlockJ5B17 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
