module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part007
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B76 : ModeBlockData :=
  ⟨⟨124, 131, (261711038477638853009/10000000000000000000000 : ℚ), (1628228715968278533/10000000000000000000000 : ℚ)⟩, [
    (124, modeDataJ4M125),
    (125, modeDataJ4M126),
    (126, modeDataJ4M127),
    (127, modeDataJ4M128),
    (128, modeDataJ4M129),
    (129, modeDataJ4M130),
    (130, modeDataJ4M131)], (130855519238819426501/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b76 : entryChecks 4 bflatBlockJ4B76.entries = true := by
  simp only [entryChecks,bflatBlockJ4B76,List.all_cons,List.all_nil,
    mode_checked_j4_m125,
    mode_checked_j4_m126,
    mode_checked_j4_m127,
    mode_checked_j4_m128,
    mode_checked_j4_m129,
    mode_checked_j4_m130,
    mode_checked_j4_m131,Bool.and_self]
theorem block_mass_checked_j4_b76 : blockMassCheck bflatBlockJ4B76 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
