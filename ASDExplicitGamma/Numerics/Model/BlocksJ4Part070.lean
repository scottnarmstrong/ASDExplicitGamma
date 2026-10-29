module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B70 : ModeBlockData :=
  ⟨⟨90, 95, (262254898485228104033/10000000000000000000000 : ℚ), (177144955122988121/1250000000000000000000 : ℚ)⟩, [
    (90, modeDataJ4M91),
    (91, modeDataJ4M92),
    (92, modeDataJ4M93),
    (93, modeDataJ4M94),
    (94, modeDataJ4M95)], (65563724621307026007/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b70 : entryChecks 4 bflatBlockJ4B70.entries = true := by
  simp only [entryChecks,bflatBlockJ4B70,List.all_cons,List.all_nil,
    mode_checked_j4_m91,
    mode_checked_j4_m92,
    mode_checked_j4_m93,
    mode_checked_j4_m94,
    mode_checked_j4_m95,Bool.and_self]
theorem block_mass_checked_j4_b70 : blockMassCheck bflatBlockJ4B70 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
