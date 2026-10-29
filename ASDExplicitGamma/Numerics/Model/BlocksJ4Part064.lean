module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B64 : ModeBlockData :=
  ⟨⟨64, 68, (50264796451520316623/2000000000000000000000 : ℚ), (632900258817958649/5000000000000000000000 : ℚ)⟩, [
    (64, modeDataJ4M65),
    (65, modeDataJ4M66),
    (66, modeDataJ4M67),
    (67, modeDataJ4M68)], (251323982257601583111/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b64 : entryChecks 4 bflatBlockJ4B64.entries = true := by
  simp only [entryChecks,bflatBlockJ4B64,List.all_cons,List.all_nil,
    mode_checked_j4_m65,
    mode_checked_j4_m66,
    mode_checked_j4_m67,
    mode_checked_j4_m68,Bool.and_self]
theorem block_mass_checked_j4_b64 : blockMassCheck bflatBlockJ4B64 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
