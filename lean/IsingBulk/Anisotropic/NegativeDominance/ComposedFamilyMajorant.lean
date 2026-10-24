import IsingBulk.Anisotropic.NegativeDominance.AnalyticJetComposition
import IsingBulk.Anisotropic.NegativeDominance.TailTannery

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter
open scoped Topology BigOperators

/-- Uniform summable jet envelopes are preserved by an analytic change of
coordinate. The finite-order composition bound is proved in the preceding module. -/
theorem composed_family_summable_jet_majorant
    {ι : Type*} {l : Filter ι} {path : ι → ℂ} {f : ℂ → ℂ} {g : ℕ → ℂ → ℂ}
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f V) (hg : ∀ n, AnalyticOnNhd ℂ (g n) U)
    (hmap : MapsTo f V U) (hin : ∀ᶠ t in l, path t∈V)
    (j : ℕ) (G : ℕ → ℕ → ℝ) (hG : ∀ i, Summable (G i))
    (hjets : ∀ i, ∀ᶠ t in l, ∀ n, ‖iteratedDeriv i (g n) (f (path t))‖≤G i n)
    {D : ℝ} (hD : ∀ᶠ t in l, ∀ i, 1 ≤ i → i≤j → ‖iteratedDeriv i f (path t)‖≤D^i) :
    ∃ H : ℕ → ℝ, Summable H ∧ ∀ᶠ t in l, ∀ n,
      ‖iteratedDeriv j (fun z => g n (f z)) (path t)‖≤H n := by
  let R : ℕ → ℝ := fun n => ∑ i∈Finset.range (j+1), ‖G i n‖
  have hR : Summable R := by
    apply summable_sum
    intro i _
    exact (summable_norm_iff).mpr (hG i)
  refine ⟨fun n => ((j.factorial : ℝ)*D^j)*R n,hR.mul_left _,?_⟩
  have hjets' : ∀ᶠ t in l, ∀ i∈Finset.range (j+1), ∀ n,
      ‖iteratedDeriv i (g n) (f (path t))‖≤G i n := by
    rw [eventually_all_finset]
    intro i _
    exact hjets i
  filter_upwards [hin,hD,hjets'] with t ht hd hj n
  have hC (i : ℕ) (hi : i≤j) : ‖iteratedDeriv i (g n) (f (path t))‖≤R n := by
    have hm : i∈Finset.range (j+1) := Finset.mem_range.mpr (by omega)
    exact (hj i hm n).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun k _ => norm_nonneg (G k n)) hm))
  have hh := analytic_jet_comp_norm_bound hV hU hf (hg n) hmap ht j hC hd
  convert hh using 1
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
