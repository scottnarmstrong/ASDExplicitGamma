module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B48 : ModeBlockData :=
  ⟨⟨48, 49, (24941011763040993347/10000000000000000000000 : ℚ), (39236441824762693/10000000000000000000000 : ℚ)⟩, [
    (48, modeDataJ5M49)], (12470505881520496673/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b48 : entryChecks 5 bflatBlockJ5B48.entries = true := by
  simp only [entryChecks,bflatBlockJ5B48,List.all_cons,List.all_nil,
    mode_checked_j5_m49,Bool.and_self]
theorem block_mass_checked_j5_b48 : blockMassCheck bflatBlockJ5B48 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
