module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B45 : ModeBlockData :=
  ⟨⟨45, 46, (629993809238408773/2500000000000000000000 : ℚ), (2054710559267672677/10000000000000000000000 : ℚ)⟩, [
    (45, modeDataJ2M46)], (2519975236953635091/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b45 : entryChecks 2 bflatBlockJ2B45.entries = true := by
  simp only [entryChecks,bflatBlockJ2B45,List.all_cons,List.all_nil,
    mode_checked_j2_m46,Bool.and_self]
theorem block_mass_checked_j2_b45 : blockMassCheck bflatBlockJ2B45 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
