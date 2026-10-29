module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part009
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part010

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B80 : ModeBlockData :=
  ⟨⟨153, 161, (204186673945447743599/10000000000000000000000 : ℚ), (1510981376687877659/10000000000000000000000 : ℚ)⟩, [
    (153, modeDataJ4M154),
    (154, modeDataJ4M155),
    (155, modeDataJ4M156),
    (156, modeDataJ4M157),
    (157, modeDataJ4M158),
    (158, modeDataJ4M159),
    (159, modeDataJ4M160),
    (160, modeDataJ4M161)], (204186673945447743591/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b80 : entryChecks 4 bflatBlockJ4B80.entries = true := by
  simp only [entryChecks,bflatBlockJ4B80,List.all_cons,List.all_nil,
    mode_checked_j4_m154,
    mode_checked_j4_m155,
    mode_checked_j4_m156,
    mode_checked_j4_m157,
    mode_checked_j4_m158,
    mode_checked_j4_m159,
    mode_checked_j4_m160,
    mode_checked_j4_m161,Bool.and_self]
theorem block_mass_checked_j4_b80 : blockMassCheck bflatBlockJ4B80 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
