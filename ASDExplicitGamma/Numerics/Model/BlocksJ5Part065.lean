module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B65 : ModeBlockData :=
  ⟨⟨71, 79, (19648833118847729773/1000000000000000000000 : ℚ), (310850525971296381/10000000000000000000000 : ℚ)⟩, [
    (71, modeDataJ5M72),
    (72, modeDataJ5M73),
    (73, modeDataJ5M74),
    (74, modeDataJ5M75),
    (75, modeDataJ5M76),
    (76, modeDataJ5M77),
    (77, modeDataJ5M78),
    (78, modeDataJ5M79)], (98244165594238648861/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b65 : entryChecks 5 bflatBlockJ5B65.entries = true := by
  simp only [entryChecks,bflatBlockJ5B65,List.all_cons,List.all_nil,
    mode_checked_j5_m72,
    mode_checked_j5_m73,
    mode_checked_j5_m74,
    mode_checked_j5_m75,
    mode_checked_j5_m76,
    mode_checked_j5_m77,
    mode_checked_j5_m78,
    mode_checked_j5_m79,Bool.and_self]
theorem block_mass_checked_j5_b65 : blockMassCheck bflatBlockJ5B65 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
