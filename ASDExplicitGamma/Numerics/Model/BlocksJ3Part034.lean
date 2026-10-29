module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B34 : ModeBlockData :=
  ⟨⟨34, 35, (142429154590699125153/10000000000000000000000 : ℚ), (2399287200617272559/10000000000000000000000 : ℚ)⟩, [
    (34, modeDataJ3M35)], (4450911080959347661/312500000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b34 : entryChecks 3 bflatBlockJ3B34.entries = true := by
  simp only [entryChecks,bflatBlockJ3B34,List.all_cons,List.all_nil,
    mode_checked_j3_m35,Bool.and_self]
theorem block_mass_checked_j3_b34 : blockMassCheck bflatBlockJ3B34 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
