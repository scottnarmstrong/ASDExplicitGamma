module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B74 : ModeBlockData :=
  ⟨⟨84, 86, (2416208719910683403/1250000000000000000000 : ℚ), (177588119875360921/1250000000000000000000 : ℚ)⟩, [
    (84, modeDataJ3M85),
    (85, modeDataJ3M86)], (9664834879642733611/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b74 : entryChecks 3 bflatBlockJ3B74.entries = true := by
  simp only [entryChecks,bflatBlockJ3B74,List.all_cons,List.all_nil,
    mode_checked_j3_m85,
    mode_checked_j3_m86,Bool.and_self]
theorem block_mass_checked_j3_b74 : blockMassCheck bflatBlockJ3B74 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
