module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B34 : ModeBlockData :=
  ⟨⟨34, 35, (6930199030002297531/10000000000000000000000 : ℚ), (96492275116645367/250000000000000000000 : ℚ)⟩, [
    (34, modeDataJ2M35)], (693019903000229753/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b34 : entryChecks 2 bflatBlockJ2B34.entries = true := by
  simp only [entryChecks,bflatBlockJ2B34,List.all_cons,List.all_nil,
    mode_checked_j2_m35,Bool.and_self]
theorem block_mass_checked_j2_b34 : blockMassCheck bflatBlockJ2B34 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
