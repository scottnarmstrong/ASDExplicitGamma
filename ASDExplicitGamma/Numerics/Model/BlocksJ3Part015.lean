module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B15 : ModeBlockData :=
  ⟨⟨15, 16, (103122889023448514413/5000000000000000000000 : ℚ), (3011372933136049539/10000000000000000000000 : ℚ)⟩, [
    (15, modeDataJ3M16)], (8249831121875881153/400000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b15 : entryChecks 3 bflatBlockJ3B15.entries = true := by
  simp only [entryChecks,bflatBlockJ3B15,List.all_cons,List.all_nil,
    mode_checked_j3_m16,Bool.and_self]
theorem block_mass_checked_j3_b15 : blockMassCheck bflatBlockJ3B15 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
