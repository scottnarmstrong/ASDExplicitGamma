module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B0 : ModeBlockData :=
  ⟨⟨0, 1, (4978487355335405191059/10000000000000000000000 : ℚ), (981665775258399328753/5000000000000000000000 : ℚ)⟩, [
    (0, modeDataJ0M1)], (2489243677667702595529/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b0 : entryChecks 0 bflatBlockJ0B0.entries = true := by
  simp only [entryChecks,bflatBlockJ0B0,List.all_cons,List.all_nil,
    mode_checked_j0_m1,Bool.and_self]
theorem block_mass_checked_j0_b0 : blockMassCheck bflatBlockJ0B0 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
