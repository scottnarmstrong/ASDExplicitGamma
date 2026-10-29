module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B20 : ModeBlockData :=
  ⟨⟨20, 21, (192351478331517965283/10000000000000000000000 : ℚ), (2882211607766578833/10000000000000000000000 : ℚ)⟩, [
    (20, modeDataJ3M21)], (96175739165758982641/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b20 : entryChecks 3 bflatBlockJ3B20.entries = true := by
  simp only [entryChecks,bflatBlockJ3B20,List.all_cons,List.all_nil,
    mode_checked_j3_m21,Bool.and_self]
theorem block_mass_checked_j3_b20 : blockMassCheck bflatBlockJ3B20 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
