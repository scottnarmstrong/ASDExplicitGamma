module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B58 : ModeBlockData :=
  ⟨⟨58, 59, (28530647156273504481/5000000000000000000000 : ℚ), (1454829809444604721/10000000000000000000000 : ℚ)⟩, [
    (58, modeDataJ3M59)], (57061294312547008961/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b58 : entryChecks 3 bflatBlockJ3B58.entries = true := by
  simp only [entryChecks,bflatBlockJ3B58,List.all_cons,List.all_nil,
    mode_checked_j3_m59,Bool.and_self]
theorem block_mass_checked_j3_b58 : blockMassCheck bflatBlockJ3B58 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
