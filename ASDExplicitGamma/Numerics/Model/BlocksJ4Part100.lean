module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part026
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part027
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part028

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B100 : ModeBlockData :=
  ⟨⟨427, 449, (304894922178801197/2500000000000000000000 : ℚ), (493844927864821033/10000000000000000000000 : ℚ)⟩, [
    (427, modeDataJ4M428),
    (428, modeDataJ4M429),
    (429, modeDataJ4M430),
    (430, modeDataJ4M431),
    (431, modeDataJ4M432),
    (432, modeDataJ4M433),
    (433, modeDataJ4M434),
    (434, modeDataJ4M435),
    (435, modeDataJ4M436),
    (436, modeDataJ4M437),
    (437, modeDataJ4M438),
    (438, modeDataJ4M439),
    (439, modeDataJ4M440),
    (440, modeDataJ4M441),
    (441, modeDataJ4M442),
    (442, modeDataJ4M443),
    (443, modeDataJ4M444),
    (444, modeDataJ4M445),
    (445, modeDataJ4M446),
    (446, modeDataJ4M447),
    (447, modeDataJ4M448),
    (448, modeDataJ4M449)], (609789844357602383/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b100 : entryChecks 4 bflatBlockJ4B100.entries = true := by
  simp only [entryChecks,bflatBlockJ4B100,List.all_cons,List.all_nil,
    mode_checked_j4_m428,
    mode_checked_j4_m429,
    mode_checked_j4_m430,
    mode_checked_j4_m431,
    mode_checked_j4_m432,
    mode_checked_j4_m433,
    mode_checked_j4_m434,
    mode_checked_j4_m435,
    mode_checked_j4_m436,
    mode_checked_j4_m437,
    mode_checked_j4_m438,
    mode_checked_j4_m439,
    mode_checked_j4_m440,
    mode_checked_j4_m441,
    mode_checked_j4_m442,
    mode_checked_j4_m443,
    mode_checked_j4_m444,
    mode_checked_j4_m445,
    mode_checked_j4_m446,
    mode_checked_j4_m447,
    mode_checked_j4_m448,
    mode_checked_j4_m449,Bool.and_self]
theorem block_mass_checked_j4_b100 : blockMassCheck bflatBlockJ4B100 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
