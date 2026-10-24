import IsingBulk.Anisotropic.RegularEdges.PhaseJets
import IsingBulk.Anisotropic.RegularEdges.ProductGap
import IsingBulk.Anisotropic.Geometry.PrimePhases

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology BigOperators

theorem edgeRoot_norm_eq_one_iff {b : ℝ} {B : ℂ} (hb : |b|<1) (hB : 0<B.im)
    {q : ℝ} (hq : q∈Icc (-Real.pi) Real.pi) : ‖edgeRoot b B q‖=1 ↔ q=0 := by
  constructor
  · intro hn
    by_contra hq0
    have hc : Real.cos q≠1 := by
      intro he
      exact hq0 ((Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [Real.pi_pos,hq.1]) (by linarith [Real.pi_pos,hq.2])).mp he)
    have hw : 0<(edgeW b B q).im := by
      rw [edgeW_im]
      exact mul_pos hB (sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one q) hc))
    have hlt := interiorRoot_norm_lt_one hw
    rw [edgeRoot,continuedRoot_eq_interiorRoot hw] at hn
    linarith
  · rintro rfl
    simp only [edgeRoot,edgeW,Real.cos_zero,Complex.ofReal_one,sub_self,mul_zero,add_zero]
    rw [continuedRoot_compactRight_real b hb]
    exact (compactRight_real_norm_im b hb).1

/-- There is exactly one unit-modulus collision in the angular fundamental cube. -/
theorem edgeRootProduct_norm_eq_one_iff {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (q : Fin N→ℝ)
    (hq : ∀ i, q i∈Icc (-Real.pi) Real.pi) :
    ‖edgeRootProduct b B 0 q‖=1 ↔ ∀ i, q i=0 := by
  have hr : ∀ i∈(Finset.univ : Finset (Fin N)), ‖edgeRoot b (B 0) (q i)‖₊≤1 := by
    intro i _
    exact_mod_cast (edgeRoot_bounds hb hB (q i)).1
  have hh := Finset.prod_eq_one_iff_of_le_one hr
  have he : ‖edgeRootProduct b B 0 q‖₊=∏ i, ‖edgeRoot b (B 0) (q i)‖₊ := by
    apply NNReal.eq
    simp [edgeRootProduct]
  constructor
  · intro hn i
    have hn' : ‖edgeRootProduct b B 0 q‖₊=1 := by apply NNReal.eq; exact hn
    rw [he] at hn'
    have hi := hh.mp hn' i (Finset.mem_univ i)
    exact (edgeRoot_norm_eq_one_iff hb hB (hq i)).mp (congrArg (fun x : NNReal => (x:ℝ)) hi)
  · intro hi
    simp only [edgeRootProduct,hi,edgeParamRoot_zero,edgeRoot,edgeW,Real.cos_zero,
      Complex.ofReal_one,sub_self,mul_zero,add_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_pow]
    rw [continuedRoot_compactRight_real b hb,(compactRight_real_norm_im b hb).1,one_pow]

theorem edgeRootProduct_eq_one_iff {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (q : Fin N→ℝ)
    (hq : ∀ i, q i∈Icc (-Real.pi) Real.pi) :
    edgeRootProduct b B 0 q=1 ↔ (∀ i, q i=0) ∧ continuedRoot (b:ℂ)^N=1 := by
  have he (hi : ∀ i, q i=0) : edgeRootProduct b B 0 q=continuedRoot (b:ℂ)^N := by
    simp only [edgeRootProduct,hi,edgeParamRoot_zero,edgeRoot,edgeW,Real.cos_zero,
      Complex.ofReal_one,sub_self,mul_zero,add_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  constructor
  · intro hz
    have hi := (edgeRootProduct_norm_eq_one_iff hb hB q hq).mp (by rw [hz,norm_one])
    exact ⟨hi,(he hi).symm.trans hz⟩
  · rintro ⟨hi,hres⟩
    exact (he hi).trans hres

/-- All nonresonant fixed orders have no lattice pole anywhere on the complete angular cube. -/
theorem edgeRootProduct_nonresonant_ne_one {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hres : continuedRoot (b:ℂ)^N≠1)
    (q : Fin N→ℝ) (hq : ∀ i, q i∈Icc (-Real.pi) Real.pi) :
    edgeRootProduct b B 0 q≠1 := fun hz => hres ((edgeRootProduct_eq_one_iff hb hB q hq).mp hz).2


theorem edgeRootProduct_continuousAt_zero {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) (q : Fin N→ℝ) :
    ContinuousAt (fun p : ℂ × (Fin N→ℝ) => edgeRootProduct b B p.1 p.2) (0,q) := by
  apply tendsto_finsetProd
  intro i _
  have hh := edgeParamRoot_continuousAt b hc
    (show edgeParamW b B 0 (q i)∈continuedRootDomain by simpa using edgeW_domain hb hB (q i))
  exact hh.comp (x := ((0:ℂ),q)) (f := fun p : ℂ × (Fin N→ℝ) => (p.1,p.2 i))
    (continuousAt_fst.prodMk ((continuous_apply i).continuousAt.comp continuousAt_snd))

/-- At nonresonant orders the entire compact angular cube stays uniformly pole-free
in one complex parameter neighborhood. -/
theorem edgeRootProduct_nonresonant_uniform_neighborhood {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0)
    (hres : continuedRoot (b:ℂ)^N≠1) :
    ∀ᶠ u in 𝓝 (0:ℂ), ∀ q : Fin N→ℝ, (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      edgeRootProduct b B u q≠1 := by
  have hh : ∀ᶠ u in 𝓝 (0:ℂ), ∀ q∈univ.pi (fun _ : Fin N => Icc (-Real.pi) Real.pi),
      edgeRootProduct b B u q≠1 := by
    apply (isCompact_univ_pi (fun _ => isCompact_Icc)).eventually_forall_of_forall_eventually
    intro q hq
    exact (edgeRootProduct_continuousAt_zero hb hB hc q).eventually_ne
      (edgeRootProduct_nonresonant_ne_one hb hB hres q (fun i => hq i (mem_univ i)))
  filter_upwards [hh] with u hu q hq
  exact hu q (fun i _ => hq i)

/-- At a resonant order, no other collision chart appears: the complement of any
fixed neighborhood of the zero-angle configuration remains uniformly pole-free. -/
theorem edgeRootProduct_away_collision_uniform_neighborhood {N : ℕ} {b : ℝ} {B : ℂ→ℂ}
    (hb : |b|<1) (hB : 0<(B 0).im) (hc : ContinuousAt B 0) {U : Set (Fin N→ℝ)}
    (hU : IsOpen U) (h0 : 0∈U) :
    ∀ᶠ u in 𝓝 (0:ℂ), ∀ q : Fin N→ℝ, (∀ i, q i∈Icc (-Real.pi) Real.pi) → q∉U →
      edgeRootProduct b B u q≠1 := by
  have hh : ∀ᶠ u in 𝓝 (0:ℂ), ∀ q∈(univ.pi (fun _ : Fin N => Icc (-Real.pi) Real.pi))\U,
      edgeRootProduct b B u q≠1 := by
    apply ((isCompact_univ_pi (fun _ => isCompact_Icc)).diff hU).eventually_forall_of_forall_eventually
    intro q hq
    apply (edgeRootProduct_continuousAt_zero hb hB hc q).eventually_ne
    intro he
    have hz := ((edgeRootProduct_eq_one_iff hb hB q (fun i => hq.1 i (mem_univ i))).mp he).1
    exact hq.2 (show q∈U by have heq : q=0 := funext hz; rw [heq]; exact h0)
  filter_upwards [hh] with u hu q hq hqU
  exact hu q ⟨fun i _ => hq i,hqU⟩

end
end IsingBulk.Anisotropic.RegularEdges
