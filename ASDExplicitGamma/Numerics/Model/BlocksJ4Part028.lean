module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B28 : ModeBlockData :=
  ⟨⟨28, 29, (73052312784941576217/10000000000000000000000 : ℚ), (347793282317755883/10000000000000000000000 : ℚ)⟩, [
    (28, modeDataJ4M29)], (9131539098117697027/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b28 : entryChecks 4 bflatBlockJ4B28.entries = true := by
  simp only [entryChecks,bflatBlockJ4B28,List.all_cons,List.all_nil,
    mode_checked_j4_m29,Bool.and_self]
theorem block_mass_checked_j4_b28 : blockMassCheck bflatBlockJ4B28 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
