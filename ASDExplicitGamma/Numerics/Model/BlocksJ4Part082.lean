module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part010
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part011

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B82 : ModeBlockData :=
  ⟨⟨170, 179, (174903544129458632567/10000000000000000000000 : ℚ), (46226923149826713/312500000000000000000 : ℚ)⟩, [
    (170, modeDataJ4M171),
    (171, modeDataJ4M172),
    (172, modeDataJ4M173),
    (173, modeDataJ4M174),
    (174, modeDataJ4M175),
    (175, modeDataJ4M176),
    (176, modeDataJ4M177),
    (177, modeDataJ4M178),
    (178, modeDataJ4M179)], (87451772064729316279/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b82 : entryChecks 4 bflatBlockJ4B82.entries = true := by
  simp only [entryChecks,bflatBlockJ4B82,List.all_cons,List.all_nil,
    mode_checked_j4_m171,
    mode_checked_j4_m172,
    mode_checked_j4_m173,
    mode_checked_j4_m174,
    mode_checked_j4_m175,
    mode_checked_j4_m176,
    mode_checked_j4_m177,
    mode_checked_j4_m178,
    mode_checked_j4_m179,Bool.and_self]
theorem block_mass_checked_j4_b82 : blockMassCheck bflatBlockJ4B82 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
