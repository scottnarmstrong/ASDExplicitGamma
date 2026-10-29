module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B11 : ModeBlockData :=
  ⟨⟨11, 12, (43019223679171138101/2000000000000000000000 : ℚ), (3092660291441317037/10000000000000000000000 : ℚ)⟩, [
    (11, modeDataJ3M12)], (26887014799481961313/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b11 : entryChecks 3 bflatBlockJ3B11.entries = true := by
  simp only [entryChecks,bflatBlockJ3B11,List.all_cons,List.all_nil,
    mode_checked_j3_m12,Bool.and_self]
theorem block_mass_checked_j3_b11 : blockMassCheck bflatBlockJ3B11 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
