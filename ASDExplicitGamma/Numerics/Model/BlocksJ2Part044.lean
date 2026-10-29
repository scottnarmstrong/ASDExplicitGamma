module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B44 : ModeBlockData :=
  ⟨⟨44, 45, (2615843082662415419/10000000000000000000000 : ℚ), (1077334973181966471/5000000000000000000000 : ℚ)⟩, [
    (44, modeDataJ2M45)], (1307921541331207709/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b44 : entryChecks 2 bflatBlockJ2B44.entries = true := by
  simp only [entryChecks,bflatBlockJ2B44,List.all_cons,List.all_nil,
    mode_checked_j2_m45,Bool.and_self]
theorem block_mass_checked_j2_b44 : blockMassCheck bflatBlockJ2B44 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
