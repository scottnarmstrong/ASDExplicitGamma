module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part024
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part025

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B98 : ModeBlockData :=
  ⟨⟨386, 406, (279666436377655609/2500000000000000000000 : ℚ), (278823189004155299/5000000000000000000000 : ℚ)⟩, [
    (386, modeDataJ4M387),
    (387, modeDataJ4M388),
    (388, modeDataJ4M389),
    (389, modeDataJ4M390),
    (390, modeDataJ4M391),
    (391, modeDataJ4M392),
    (392, modeDataJ4M393),
    (393, modeDataJ4M394),
    (394, modeDataJ4M395),
    (395, modeDataJ4M396),
    (396, modeDataJ4M397),
    (397, modeDataJ4M398),
    (398, modeDataJ4M399),
    (399, modeDataJ4M400),
    (400, modeDataJ4M401),
    (401, modeDataJ4M402),
    (402, modeDataJ4M403),
    (403, modeDataJ4M404),
    (404, modeDataJ4M405),
    (405, modeDataJ4M406)], (69916609094413901/625000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b98 : entryChecks 4 bflatBlockJ4B98.entries = true := by
  simp only [entryChecks,bflatBlockJ4B98,List.all_cons,List.all_nil,
    mode_checked_j4_m387,
    mode_checked_j4_m388,
    mode_checked_j4_m389,
    mode_checked_j4_m390,
    mode_checked_j4_m391,
    mode_checked_j4_m392,
    mode_checked_j4_m393,
    mode_checked_j4_m394,
    mode_checked_j4_m395,
    mode_checked_j4_m396,
    mode_checked_j4_m397,
    mode_checked_j4_m398,
    mode_checked_j4_m399,
    mode_checked_j4_m400,
    mode_checked_j4_m401,
    mode_checked_j4_m402,
    mode_checked_j4_m403,
    mode_checked_j4_m404,
    mode_checked_j4_m405,
    mode_checked_j4_m406,Bool.and_self]
theorem block_mass_checked_j4_b98 : blockMassCheck bflatBlockJ4B98 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
