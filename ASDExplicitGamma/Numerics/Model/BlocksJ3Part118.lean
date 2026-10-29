module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part014

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B118 : ModeBlockData :=
  ⟨⟨234, 239, (188700233277332431/5000000000000000000000 : ℚ), (368691892025883571/10000000000000000000000 : ℚ)⟩, [
    (234, modeDataJ3M235),
    (235, modeDataJ3M236),
    (236, modeDataJ3M237),
    (237, modeDataJ3M238),
    (238, modeDataJ3M239)], (377400466554664857/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b118 : entryChecks 3 bflatBlockJ3B118.entries = true := by
  simp only [entryChecks,bflatBlockJ3B118,List.all_cons,List.all_nil,
    mode_checked_j3_m235,
    mode_checked_j3_m236,
    mode_checked_j3_m237,
    mode_checked_j3_m238,
    mode_checked_j3_m239,Bool.and_self]
theorem block_mass_checked_j3_b118 : blockMassCheck bflatBlockJ3B118 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
