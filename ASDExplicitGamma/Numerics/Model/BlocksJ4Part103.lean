module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part031

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B103 : ModeBlockData :=
  ⟨⟨496, 512, (168086940521452049/5000000000000000000000 : ℚ), (8337634915232223/312500000000000000000 : ℚ)⟩, [
    (496, modeDataJ4M497),
    (497, modeDataJ4M498),
    (498, modeDataJ4M499),
    (499, modeDataJ4M500),
    (500, modeDataJ4M501),
    (501, modeDataJ4M502),
    (502, modeDataJ4M503),
    (503, modeDataJ4M504),
    (504, modeDataJ4M505),
    (505, modeDataJ4M506),
    (506, modeDataJ4M507),
    (507, modeDataJ4M508),
    (508, modeDataJ4M509),
    (509, modeDataJ4M510),
    (510, modeDataJ4M511),
    (511, modeDataJ4M512)], (168086940521452041/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b103 : entryChecks 4 bflatBlockJ4B103.entries = true := by
  simp only [entryChecks,bflatBlockJ4B103,List.all_cons,List.all_nil,
    mode_checked_j4_m497,
    mode_checked_j4_m498,
    mode_checked_j4_m499,
    mode_checked_j4_m500,
    mode_checked_j4_m501,
    mode_checked_j4_m502,
    mode_checked_j4_m503,
    mode_checked_j4_m504,
    mode_checked_j4_m505,
    mode_checked_j4_m506,
    mode_checked_j4_m507,
    mode_checked_j4_m508,
    mode_checked_j4_m509,
    mode_checked_j4_m510,
    mode_checked_j4_m511,
    mode_checked_j4_m512,Bool.and_self]
theorem block_mass_checked_j4_b103 : blockMassCheck bflatBlockJ4B103 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
