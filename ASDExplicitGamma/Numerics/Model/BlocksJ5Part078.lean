module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part016
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part017

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B78 : ModeBlockData :=
  ⟨⟨260, 287, (477938846366731125787/10000000000000000000000 : ℚ), (107129609573306037/1250000000000000000000 : ℚ)⟩, [
    (260, modeDataJ5M261),
    (261, modeDataJ5M262),
    (262, modeDataJ5M263),
    (263, modeDataJ5M264),
    (264, modeDataJ5M265),
    (265, modeDataJ5M266),
    (266, modeDataJ5M267),
    (267, modeDataJ5M268),
    (268, modeDataJ5M269),
    (269, modeDataJ5M270),
    (270, modeDataJ5M271),
    (271, modeDataJ5M272),
    (272, modeDataJ5M273),
    (273, modeDataJ5M274),
    (274, modeDataJ5M275),
    (275, modeDataJ5M276),
    (276, modeDataJ5M277),
    (277, modeDataJ5M278),
    (278, modeDataJ5M279),
    (279, modeDataJ5M280),
    (280, modeDataJ5M281),
    (281, modeDataJ5M282),
    (282, modeDataJ5M283),
    (283, modeDataJ5M284),
    (284, modeDataJ5M285),
    (285, modeDataJ5M286),
    (286, modeDataJ5M287)], (93347430931002173/1953125000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b78 : entryChecks 5 bflatBlockJ5B78.entries = true := by
  simp only [entryChecks,bflatBlockJ5B78,List.all_cons,List.all_nil,
    mode_checked_j5_m261,
    mode_checked_j5_m262,
    mode_checked_j5_m263,
    mode_checked_j5_m264,
    mode_checked_j5_m265,
    mode_checked_j5_m266,
    mode_checked_j5_m267,
    mode_checked_j5_m268,
    mode_checked_j5_m269,
    mode_checked_j5_m270,
    mode_checked_j5_m271,
    mode_checked_j5_m272,
    mode_checked_j5_m273,
    mode_checked_j5_m274,
    mode_checked_j5_m275,
    mode_checked_j5_m276,
    mode_checked_j5_m277,
    mode_checked_j5_m278,
    mode_checked_j5_m279,
    mode_checked_j5_m280,
    mode_checked_j5_m281,
    mode_checked_j5_m282,
    mode_checked_j5_m283,
    mode_checked_j5_m284,
    mode_checked_j5_m285,
    mode_checked_j5_m286,
    mode_checked_j5_m287,Bool.and_self]
theorem block_mass_checked_j5_b78 : blockMassCheck bflatBlockJ5B78 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
