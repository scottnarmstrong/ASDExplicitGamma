module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B3 : ModeBlockData :=
  ⟨⟨3, 4, (367241866525801287347/10000000000000000000000 : ℚ), (291727665109709916793/10000000000000000000000 : ℚ)⟩, [
    (3, modeDataJ0M4)], (183620933262900643673/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b3 : entryChecks 0 bflatBlockJ0B3.entries = true := by
  simp only [entryChecks,bflatBlockJ0B3,List.all_cons,List.all_nil,
    mode_checked_j0_m4,Bool.and_self]
theorem block_mass_checked_j0_b3 : blockMassCheck bflatBlockJ0B3 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
