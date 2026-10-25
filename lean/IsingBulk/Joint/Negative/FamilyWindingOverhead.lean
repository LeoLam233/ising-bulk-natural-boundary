import IsingBulk.Joint.Negative.FamilyWindingLogBounds

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_winding_overhead (B rootB : ℂ × E→ℂ) (phi M c : ℝ)
    {Q : Set E} (hQ : IsCompact Q) (hB : ∀eta∈Q,AnalyticAt ℂ B (0,eta))
    (hBn : ∀eta∈Q,B (0,eta)≠0) (hroot : ∀eta∈Q,AnalyticAt ℂ rootB (0,eta))
    (hrootn : ∀eta∈Q,rootB (0,eta)≠0) (hs : Real.sin phi≠0) (hM : 1≤M) (hc : 0<c) :
    ∃C : ℝ,0<C ∧ ∀ᶠN : ℕ in atTop,∀eta∈Q,
      higherWindingOverhead M c (B (tau N,eta)) (rootB (tau N,eta))
        (hessianFactor (B (tau N,eta)) (Real.cos phi) (Real.sin phi) N) (Real.sin phi) N≤
          Real.exp (C*(N:ℝ)^2) := by
  obtain ⟨L₀,hL₀,hdata⟩ := compact_family_winding_log_bounds B rootB phi hQ hB hBn hroot hrootn
  let L := L₀+1+|Real.log M|+|Real.log c|+|Real.log (|Real.sin phi|)|+
    |Real.log (2*Real.pi)|+|Real.log 2|
  have hLs : 1≤L ∧ L₀≤L ∧ Real.log M≤L ∧ |Real.log c|≤L ∧
      |Real.log (|Real.sin phi|)|≤L ∧ Real.log (2*Real.pi)≤L ∧ Real.log 2≤L := by
    dsimp [L]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
      linarith only [hL₀,abs_nonneg (Real.log M),abs_nonneg (Real.log c),
        abs_nonneg (Real.log (|Real.sin phi|)),abs_nonneg (Real.log (2*Real.pi)),
        abs_nonneg (Real.log 2),le_abs_self (Real.log M),
        le_abs_self (Real.log (2*Real.pi)),le_abs_self (Real.log 2)]
  refine ⟨20*(L+1),by linarith [hLs.1],?_⟩
  filter_upwards [hdata,eventually_ge_atTop (2:ℕ)] with N hdata hN eta heta
  obtain ⟨hb,hr,hh,hlb,hlr,hlh⟩ := hdata eta heta
  exact higherWindingOverhead_entropy M c _ _ _ (Real.sin phi) L hN hM hc hb hr hh hs hLs.1
    hLs.2.2.1 hLs.2.2.2.1 (hlb.trans hLs.2.1) (hlr.trans hLs.2.1)
    ((le_abs_self _).trans (hlh.trans hLs.2.1)) hLs.2.2.2.2.1 hLs.2.2.2.2.2.1 hLs.2.2.2.2.2.2

end
end IsingBulk.Joint.Negative
