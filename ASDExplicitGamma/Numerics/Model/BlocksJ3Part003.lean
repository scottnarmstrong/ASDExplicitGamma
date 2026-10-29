module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B3 : ModeBlockData :=
  ⟨⟨3, 4, (112817123286580058737/5000000000000000000000 : ℚ), (3188521857998773941/10000000000000000000000 : ℚ)⟩, [
    (3, modeDataJ3M4)], (225634246573160117473/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b3 : entryChecks 3 bflatBlockJ3B3.entries = true := by
  simp only [entryChecks,bflatBlockJ3B3,List.all_cons,List.all_nil,
    mode_checked_j3_m4,Bool.and_self]
theorem block_mass_checked_j3_b3 : blockMassCheck bflatBlockJ3B3 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
