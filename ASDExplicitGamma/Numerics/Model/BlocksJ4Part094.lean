module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part019
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part020

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B94 : ModeBlockData :=
  ⟨⟨316, 332, (2984981169600853723/10000000000000000000000 : ℚ), (177354926186542509/2500000000000000000000 : ℚ)⟩, [
    (316, modeDataJ4M317),
    (317, modeDataJ4M318),
    (318, modeDataJ4M319),
    (319, modeDataJ4M320),
    (320, modeDataJ4M321),
    (321, modeDataJ4M322),
    (322, modeDataJ4M323),
    (323, modeDataJ4M324),
    (324, modeDataJ4M325),
    (325, modeDataJ4M326),
    (326, modeDataJ4M327),
    (327, modeDataJ4M328),
    (328, modeDataJ4M329),
    (329, modeDataJ4M330),
    (330, modeDataJ4M331),
    (331, modeDataJ4M332)], (2984981169600853707/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b94 : entryChecks 4 bflatBlockJ4B94.entries = true := by
  simp only [entryChecks,bflatBlockJ4B94,List.all_cons,List.all_nil,
    mode_checked_j4_m317,
    mode_checked_j4_m318,
    mode_checked_j4_m319,
    mode_checked_j4_m320,
    mode_checked_j4_m321,
    mode_checked_j4_m322,
    mode_checked_j4_m323,
    mode_checked_j4_m324,
    mode_checked_j4_m325,
    mode_checked_j4_m326,
    mode_checked_j4_m327,
    mode_checked_j4_m328,
    mode_checked_j4_m329,
    mode_checked_j4_m330,
    mode_checked_j4_m331,
    mode_checked_j4_m332,Bool.and_self]
theorem block_mass_checked_j4_b94 : blockMassCheck bflatBlockJ4B94 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
