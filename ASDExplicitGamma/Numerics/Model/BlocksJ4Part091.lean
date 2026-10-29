module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part016
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part017

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B91 : ModeBlockData :=
  ⟨⟨271, 285, (1284781918397476439/625000000000000000000 : ℚ), (453155327274720357/5000000000000000000000 : ℚ)⟩, [
    (271, modeDataJ4M272),
    (272, modeDataJ4M273),
    (273, modeDataJ4M274),
    (274, modeDataJ4M275),
    (275, modeDataJ4M276),
    (276, modeDataJ4M277),
    (277, modeDataJ4M278),
    (278, modeDataJ4M279),
    (279, modeDataJ4M280),
    (280, modeDataJ4M281),
    (281, modeDataJ4M282),
    (282, modeDataJ4M283),
    (283, modeDataJ4M284),
    (284, modeDataJ4M285)], (2055651069435962301/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b91 : entryChecks 4 bflatBlockJ4B91.entries = true := by
  simp only [entryChecks,bflatBlockJ4B91,List.all_cons,List.all_nil,
    mode_checked_j4_m272,
    mode_checked_j4_m273,
    mode_checked_j4_m274,
    mode_checked_j4_m275,
    mode_checked_j4_m276,
    mode_checked_j4_m277,
    mode_checked_j4_m278,
    mode_checked_j4_m279,
    mode_checked_j4_m280,
    mode_checked_j4_m281,
    mode_checked_j4_m282,
    mode_checked_j4_m283,
    mode_checked_j4_m284,
    mode_checked_j4_m285,Bool.and_self]
theorem block_mass_checked_j4_b91 : blockMassCheck bflatBlockJ4B91 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
