module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B44 : ModeBlockData :=
  ⟨⟨44, 45, (103906411251070027001/10000000000000000000000 : ℚ), (1998941644506912613/10000000000000000000000 : ℚ)⟩, [
    (44, modeDataJ3M45)], (103906411251070027/10000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b44 : entryChecks 3 bflatBlockJ3B44.entries = true := by
  simp only [entryChecks,bflatBlockJ3B44,List.all_cons,List.all_nil,
    mode_checked_j3_m45,Bool.and_self]
theorem block_mass_checked_j3_b44 : blockMassCheck bflatBlockJ3B44 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
