module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B65 : ModeBlockData :=
  ⟨⟨68, 72, (245550473244084248649/10000000000000000000000 : ℚ), (623874074092434667/5000000000000000000000 : ℚ)⟩, [
    (68, modeDataJ4M69),
    (69, modeDataJ4M70),
    (70, modeDataJ4M71),
    (71, modeDataJ4M72)], (49110094648816849729/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b65 : entryChecks 4 bflatBlockJ4B65.entries = true := by
  simp only [entryChecks,bflatBlockJ4B65,List.all_cons,List.all_nil,
    mode_checked_j4_m69,
    mode_checked_j4_m70,
    mode_checked_j4_m71,
    mode_checked_j4_m72,Bool.and_self]
theorem block_mass_checked_j4_b65 : blockMassCheck bflatBlockJ4B65 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
