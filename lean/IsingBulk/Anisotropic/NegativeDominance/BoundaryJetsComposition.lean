import IsingBulk.Anisotropic.NegativeDominance.ComposedFamilyMajorant

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem analytic_finite_jets_uniform_bound {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (j : ℕ) :
    ∃ D : ℝ, 0<D ∧ ∀ᶠ x in 𝓝 (0 : ℂ), ∀ i, 1 ≤ i → i ≤ j →
      ‖iteratedDeriv i f x‖≤D^i := by
  let D : ℝ := 1+∑ i∈Finset.range (j+1), (‖iteratedDeriv i f 0‖+1)
  have hs : 0≤∑ i∈Finset.range (j+1), (‖iteratedDeriv i f 0‖+1) :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hD : 1≤D := by dsimp [D]; linarith
  refine ⟨D,lt_of_lt_of_le zero_lt_one hD,?_⟩
  have he : ∀ᶠ x in 𝓝 (0 : ℂ), ∀ i∈Finset.range (j+1),
      ‖iteratedDeriv i f x‖≤‖iteratedDeriv i f 0‖+1 := by
    rw [eventually_all_finset]
    intro i _
    have hc : ContinuousAt (iteratedDeriv i f) 0 := by
      simpa only [iteratedDeriv_eq_iterate] using (hf.iterated_deriv i).continuousAt
    exact (hc.norm.eventually_lt continuousAt_const (lt_add_one _)).mono (fun _ h => h.le)
  filter_upwards [he] with x hx i hi hij
  have hm : i∈Finset.range (j+1) := Finset.mem_range.mpr (by omega)
  have hsum := Finset.single_le_sum (fun k (_ : k∈Finset.range (j+1)) =>
    show 0≤‖iteratedDeriv k f 0‖+1 by positivity) hm
  apply (hx i hm).trans
  apply (show ‖iteratedDeriv i f 0‖+1≤D by dsimp [D]; linarith).trans
  exact le_self_pow₀ hD (by omega)

/-- A proved stability theorem for complete boundary jets under analytic
coordinate change. Summable envelopes, not finite-index replacements, are used. -/
theorem complete_boundary_jets_comp
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {f F : ℂ → ℂ} {g h : ℕ → ℂ → ℂ} {V U : Set ℂ}
    (hV : IsOpen V) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f V)
    (hf0 : AnalyticAt ℂ f 0) (hfz : f 0=0)
    (hg : ∀ n, AnalyticOnNhd ℂ (g n) U) (hh : ∀ n, AnalyticAt ℂ (h n) 0)
    (hmap : MapsTo f V U) (heq : ∀ n u, u∈U → g n u=h n u)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈V)
    (henv : ∀ i, ∃ G : ℕ → ℝ, Summable G ∧
      ∀ᶠ t in l, ∀ n, ‖iteratedDeriv i (g n) (f (path t))‖≤G n)
    (hfull : ∀ j x, x∈V → HasSum
      (fun n => iteratedDeriv j (fun z => g n (f z)) x)
      (iteratedDeriv j (fun z => F (f z)) x)) (j : ℕ) :
    Summable (fun n => ‖iteratedDeriv j (fun z => h n (f z)) 0‖) ∧
    Tendsto (fun t => iteratedDeriv j (fun z => F (f z)) (path t)) l
      (𝓝 (∑' n, iteratedDeriv j (fun z => h n (f z)) 0)) := by
  choose G hG hbound using henv
  obtain ⟨D,_,hD⟩ := analytic_finite_jets_uniform_bound hf0 j
  obtain ⟨H,hH,hHbound⟩ := composed_family_summable_jet_majorant
    hV hU hf hg hmap hin j G hG hbound (hp.eventually hD)
  have hlim (n : ℕ) : Tendsto
      (fun t => iteratedDeriv j (fun z => g n (f z)) (path t)) l
      (𝓝 (iteratedDeriv j (fun z => h n (f z)) 0)) := by
    have ha : AnalyticAt ℂ (fun z => h n (f z)) 0 :=
      (hh n).comp_of_eq hf0 hfz
    have hc : ContinuousAt (iteratedDeriv j (fun z => h n (f z))) 0 := by
      simpa only [iteratedDeriv_eq_iterate] using (ha.iterated_deriv j).continuousAt
    apply (hc.tendsto.comp hp).congr'
    filter_upwards [hin] with t ht
    have he : (fun z => g n (f z)) =ᶠ[𝓝 (path t)] (fun z => h n (f z)) := by
      filter_upwards [hV.mem_nhds ht] with z hz
      exact heq n (f z) (hmap hz)
    exact (he.iteratedDeriv_eq j).symm
  have htail : ∀ᶠ t in l, ∀ k, ‖iteratedDeriv j (fun z => g (k+0) (f z)) (path t)‖≤H k := by
    simpa only [Nat.add_zero] using hHbound
  refine ⟨summable_of_summable_tail_limit 0 hH hlim htail,?_⟩
  apply (tendsto_tsum_of_summable_tail 0 hH hlim htail).congr'
  filter_upwards [hin] with t ht
  exact (hfull j (path t) ht).tsum_eq

end
end IsingBulk.Anisotropic.NegativeDominance
