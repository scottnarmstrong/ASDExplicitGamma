module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part011

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B83 : ModeBlockData :=
  ⟨⟨179, 189, (82503532598389153399/5000000000000000000000 : ℚ), (1517999397411213863/10000000000000000000000 : ℚ)⟩, [
    (179, modeDataJ4M180),
    (180, modeDataJ4M181),
    (181, modeDataJ4M182),
    (182, modeDataJ4M183),
    (183, modeDataJ4M184),
    (184, modeDataJ4M185),
    (185, modeDataJ4M186),
    (186, modeDataJ4M187),
    (187, modeDataJ4M188),
    (188, modeDataJ4M189)], (41251766299194576697/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b83 : entryChecks 4 bflatBlockJ4B83.entries = true := by
  simp only [entryChecks,bflatBlockJ4B83,List.all_cons,List.all_nil,
    mode_checked_j4_m180,
    mode_checked_j4_m181,
    mode_checked_j4_m182,
    mode_checked_j4_m183,
    mode_checked_j4_m184,
    mode_checked_j4_m185,
    mode_checked_j4_m186,
    mode_checked_j4_m187,
    mode_checked_j4_m188,
    mode_checked_j4_m189,Bool.and_self]
theorem block_mass_checked_j4_b83 : blockMassCheck bflatBlockJ4B83 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
