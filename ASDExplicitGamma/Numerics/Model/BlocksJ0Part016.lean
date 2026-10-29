module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B16 : ModeBlockData :=
  ⟨⟨16, 17, (14180911058840085663/10000000000000000000000 : ℚ), (112812884297569143/80000000000000000000 : ℚ)⟩, [
    (16, modeDataJ0M17)], (7090455529420042831/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b16 : entryChecks 0 bflatBlockJ0B16.entries = true := by
  simp only [entryChecks,bflatBlockJ0B16,List.all_cons,List.all_nil,
    mode_checked_j0_m17,Bool.and_self]
theorem block_mass_checked_j0_b16 : blockMassCheck bflatBlockJ0B16 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
