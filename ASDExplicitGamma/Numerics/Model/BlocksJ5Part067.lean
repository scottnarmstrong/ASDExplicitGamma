module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part005
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B67 : ModeBlockData :=
  ⟨⟨88, 97, (21803643451487072951/1000000000000000000000 : ℚ), (69336643890860739/2000000000000000000000 : ℚ)⟩, [
    (88, modeDataJ5M89),
    (89, modeDataJ5M90),
    (90, modeDataJ5M91),
    (91, modeDataJ5M92),
    (92, modeDataJ5M93),
    (93, modeDataJ5M94),
    (94, modeDataJ5M95),
    (95, modeDataJ5M96),
    (96, modeDataJ5M97)], (218036434514870729501/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b67 : entryChecks 5 bflatBlockJ5B67.entries = true := by
  simp only [entryChecks,bflatBlockJ5B67,List.all_cons,List.all_nil,
    mode_checked_j5_m89,
    mode_checked_j5_m90,
    mode_checked_j5_m91,
    mode_checked_j5_m92,
    mode_checked_j5_m93,
    mode_checked_j5_m94,
    mode_checked_j5_m95,
    mode_checked_j5_m96,
    mode_checked_j5_m97,Bool.and_self]
theorem block_mass_checked_j5_b67 : blockMassCheck bflatBlockJ5B67 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
