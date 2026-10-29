module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B47 : ModeBlockData :=
  ⟨⟨47, 48, (2304270537474619467/10000000000000000000000 : ℚ), (1875661987751179643/10000000000000000000000 : ℚ)⟩, [
    (47, modeDataJ2M48)], (1152135268737309733/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b47 : entryChecks 2 bflatBlockJ2B47.entries = true := by
  simp only [entryChecks,bflatBlockJ2B47,List.all_cons,List.all_nil,
    mode_checked_j2_m48,Bool.and_self]
theorem block_mass_checked_j2_b47 : blockMassCheck bflatBlockJ2B47 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
