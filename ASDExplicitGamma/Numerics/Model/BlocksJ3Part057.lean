module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B57 : ModeBlockData :=
  ⟨⟨57, 58, (29977830349841484173/5000000000000000000000 : ℚ), (745643483274180957/5000000000000000000000 : ℚ)⟩, [
    (57, modeDataJ3M58)], (11991132139936593669/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b57 : entryChecks 3 bflatBlockJ3B57.entries = true := by
  simp only [entryChecks,bflatBlockJ3B57,List.all_cons,List.all_nil,
    mode_checked_j3_m58,Bool.and_self]
theorem block_mass_checked_j3_b57 : blockMassCheck bflatBlockJ3B57 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
