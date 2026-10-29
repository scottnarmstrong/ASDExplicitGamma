module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part009

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B100 : ModeBlockData :=
  ⟨⟨155, 159, (57155629337983849/625000000000000000000 : ℚ), (344674404613767851/5000000000000000000000 : ℚ)⟩, [
    (155, modeDataJ3M156),
    (156, modeDataJ3M157),
    (157, modeDataJ3M158),
    (158, modeDataJ3M159)], (45724503470387079/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b100 : entryChecks 3 bflatBlockJ3B100.entries = true := by
  simp only [entryChecks,bflatBlockJ3B100,List.all_cons,List.all_nil,
    mode_checked_j3_m156,
    mode_checked_j3_m157,
    mode_checked_j3_m158,
    mode_checked_j3_m159,Bool.and_self]
theorem block_mass_checked_j3_b100 : blockMassCheck bflatBlockJ3B100 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
