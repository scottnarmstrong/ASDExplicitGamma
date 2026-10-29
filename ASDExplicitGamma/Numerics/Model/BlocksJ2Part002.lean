module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B2 : ModeBlockData :=
  ⟨⟨2, 3, (330519991487617270993/5000000000000000000000 : ℚ), (28254972751423308103/10000000000000000000000 : ℚ)⟩, [
    (2, modeDataJ2M3)], (132207996595046908397/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b2 : entryChecks 2 bflatBlockJ2B2.entries = true := by
  simp only [entryChecks,bflatBlockJ2B2,List.all_cons,List.all_nil,
    mode_checked_j2_m3,Bool.and_self]
theorem block_mass_checked_j2_b2 : blockMassCheck bflatBlockJ2B2 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
