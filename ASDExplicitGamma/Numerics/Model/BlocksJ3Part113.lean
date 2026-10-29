module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part013

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B113 : ModeBlockData :=
  ⟨⟨209, 214, (99903009541228789/2000000000000000000000 : ℚ), (115870045918594357/2500000000000000000000 : ℚ)⟩, [
    (209, modeDataJ3M210),
    (210, modeDataJ3M211),
    (211, modeDataJ3M212),
    (212, modeDataJ3M213),
    (213, modeDataJ3M214)], (24975752385307197/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b113 : entryChecks 3 bflatBlockJ3B113.entries = true := by
  simp only [entryChecks,bflatBlockJ3B113,List.all_cons,List.all_nil,
    mode_checked_j3_m210,
    mode_checked_j3_m211,
    mode_checked_j3_m212,
    mode_checked_j3_m213,
    mode_checked_j3_m214,Bool.and_self]
theorem block_mass_checked_j3_b113 : blockMassCheck bflatBlockJ3B113 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
