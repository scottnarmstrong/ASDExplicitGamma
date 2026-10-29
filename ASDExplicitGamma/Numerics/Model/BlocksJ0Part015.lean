module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ0Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ0B15 : ModeBlockData :=
  ⟨⟨15, 16, (1603251270311785017/1000000000000000000000 : ℚ), (7965474559195304689/5000000000000000000000 : ℚ)⟩, [
    (15, modeDataJ0M16)], (16032512703117850169/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j0_b15 : entryChecks 0 bflatBlockJ0B15.entries = true := by
  simp only [entryChecks,bflatBlockJ0B15,List.all_cons,List.all_nil,
    mode_checked_j0_m16,Bool.and_self]
theorem block_mass_checked_j0_b15 : blockMassCheck bflatBlockJ0B15 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
