module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B40 : ModeBlockData :=
  ⟨⟨40, 41, (1518852142555004403/5000000000000000000000 : ℚ), (2648582312710495249/10000000000000000000000 : ℚ)⟩, [
    (40, modeDataJ2M41)], (607540857022001761/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b40 : entryChecks 2 bflatBlockJ2B40.entries = true := by
  simp only [entryChecks,bflatBlockJ2B40,List.all_cons,List.all_nil,
    mode_checked_j2_m41,Bool.and_self]
theorem block_mass_checked_j2_b40 : blockMassCheck bflatBlockJ2B40 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
