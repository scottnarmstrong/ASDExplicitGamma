module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B28 : ModeBlockData :=
  ⟨⟨28, 29, (15125635412985993461/5000000000000000000000 : ℚ), (1226804348393870371/2000000000000000000000 : ℚ)⟩, [
    (28, modeDataJ2M29)], (30251270825971986921/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b28 : entryChecks 2 bflatBlockJ2B28.entries = true := by
  simp only [entryChecks,bflatBlockJ2B28,List.all_cons,List.all_nil,
    mode_checked_j2_m29,Bool.and_self]
theorem block_mass_checked_j2_b28 : blockMassCheck bflatBlockJ2B28 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
