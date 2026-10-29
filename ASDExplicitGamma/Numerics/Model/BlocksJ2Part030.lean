module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B30 : ModeBlockData :=
  ⟨⟨30, 31, (18583315184142898067/10000000000000000000000 : ℚ), (5216308571043421909/10000000000000000000000 : ℚ)⟩, [
    (30, modeDataJ2M31)], (9291657592071449033/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b30 : entryChecks 2 bflatBlockJ2B30.entries = true := by
  simp only [entryChecks,bflatBlockJ2B30,List.all_cons,List.all_nil,
    mode_checked_j2_m31,Bool.and_self]
theorem block_mass_checked_j2_b30 : blockMassCheck bflatBlockJ2B30 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
