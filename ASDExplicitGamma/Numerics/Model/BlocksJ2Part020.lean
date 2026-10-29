module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B20 : ModeBlockData :=
  ⟨⟨20, 21, (72660836735222674171/5000000000000000000000 : ℚ), (1478543230658163659/1250000000000000000000 : ℚ)⟩, [
    (20, modeDataJ2M21)], (145321673470445348341/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b20 : entryChecks 2 bflatBlockJ2B20.entries = true := by
  simp only [entryChecks,bflatBlockJ2B20,List.all_cons,List.all_nil,
    mode_checked_j2_m21,Bool.and_self]
theorem block_mass_checked_j2_b20 : blockMassCheck bflatBlockJ2B20 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
