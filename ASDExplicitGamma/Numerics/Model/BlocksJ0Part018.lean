module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B18 : ModeBlockData :=
  ⟨⟨18, 19, (5663483790993006777/5000000000000000000000 : ℚ), (2255300190404272343/2000000000000000000000 : ℚ)⟩, [
    (18, modeDataJ0M19)], (11326967581986013553/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b18 : entryChecks 0 bflatBlockJ0B18.entries = true := by
  simp only [entryChecks,bflatBlockJ0B18,List.all_cons,List.all_nil,
    mode_checked_j0_m19,Bool.and_self]
theorem block_mass_checked_j0_b18 : blockMassCheck bflatBlockJ0B18 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
