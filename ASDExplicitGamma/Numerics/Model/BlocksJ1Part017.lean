module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ1Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ1B17 : ModeBlockData :=
  ⟨⟨17, 18, (14142866381587251763/10000000000000000000000 : ℚ), (13149816864363800261/10000000000000000000000 : ℚ)⟩, [
    (17, modeDataJ1M18)], (7071433190793625881/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j1_b17 : entryChecks 1 bflatBlockJ1B17.entries = true := by
  simp only [entryChecks,bflatBlockJ1B17,List.all_cons,List.all_nil,
    mode_checked_j1_m18,Bool.and_self]
theorem block_mass_checked_j1_b17 : blockMassCheck bflatBlockJ1B17 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
