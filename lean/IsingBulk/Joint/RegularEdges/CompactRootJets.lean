import IsingBulk.Joint.RegularEdges.CompactMixedJets
import IsingBulk.Anisotropic.RegularEdges.RootGap

/-! # Compact-family root gaps and all mixed root derivatives -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set Filter Metric
open scoped Topology BigOperators

def independentRoot (b : ℝ) (p : NumeratorParameter) (q : ℝ) : ℂ := root b (p.1,p.2.1) q

theorem compact_root_disk {b : ℝ} {K : Set ℂ}
    (hb : |b|<1) (hK : IsCompact K) (hB : ∀ B∈K, 0<B.im) :
    ∃ δ : ℝ, 0<δ ∧ ∀ u B : ℂ, ‖u‖<δ → B∈K →
      ∀ q∈Icc (-Real.pi) Real.pi, ‖root b (u,B) q‖≤2 := by
  have he : ∀ᶠ u : ℂ in 𝓝 0, ∀ x∈K ×ˢ Icc (-Real.pi) Real.pi, ‖root b (u,x.1) x.2‖<2 := by
    apply (hK.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro x hx
    have hc := (root_continuousAt (show dispersion b (0,x.1) x.2∈continuedRootDomain by
      simpa using edgeW_domain hb (hB x.1 hx.1) x.2)).comp
      (x := ((0:ℂ),x)) (f := fun y : ℂ × (ℂ × ℝ) => ((y.1,y.2.1),y.2.2)) (by fun_prop)
    exact hc.norm.eventually_lt continuousAt_const
      (by simpa only [Function.comp_def,root_zero] using (edgeRoot_bounds hb (hB x.1 hx.1) x.2).1.trans_lt (by norm_num : (1:ℝ)<2))
  obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨δ,hδ,fun u B hu hBK q hq => (hδb (by simpa using hu) (B,q) ⟨hBK,hq⟩).le⟩

theorem root_gap_of_margins (b : ℝ) {u B : ℂ} {β M : ℝ}
    (hβ : 0<β) (hB : β≤B.im) (hM : 0≤M) (hBn : ‖B‖≤M)
    (hu : ‖u‖≤1) (hui : 0<u.im) {q : ℝ} (hq : q∈Icc (-Real.pi) Real.pi) :
    min 1 (2*β/Real.pi^2)/(2*(|b|+1+2*M)+1)*(u.im+q^2)≤1-‖root b (u,B) q‖ := by
  let k := 2*β/Real.pi^2
  let d := min 1 k
  let W := |b|+1+2*M
  have hk : 0<k := by dsimp [k]; positivity
  have hW : 0<W := by dsimp [W]; positivity
  have hm := edgeParamW_im_margin (B := fun _ => B) (u := u) b hβ.le hB (abs_le.mpr hq)
  have hm' : u.im+k*q^2≤(dispersion b (u,B) q).im := hm
  have hm'' : d*(u.im+q^2)≤(dispersion b (u,B) q).im := by
    have h1 := mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) k) hui.le
    have h2 := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) k) (sq_nonneg q)
    dsimp [d]
    nlinarith
  have hi : 0<(dispersion b (u,B) q).im := lt_of_lt_of_le (by positivity) hm'
  have hn : ‖dispersion b (u,B) q‖≤W := edgeParamW_norm_bound (B := fun _ => B) b hu hBn q
  have hh := (div_le_div_of_nonneg_right hm'' (by positivity : 0≤2*W+1)).trans
    (interiorRoot_modulus_gap hi hn)
  simpa only [root,continuedRoot_eq_interiorRoot hi,div_mul_eq_mul_div] using hh

/-- One independent-parameter polydisk, chosen before all derivative orders,
with a uniform retained quadratic root gap on its upper side. -/
theorem compact_roots_polydisks {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ c : ℝ, 0<δ ∧ 0<c ∧ ∀ v∈K,
      (∀ p∈ball ((0:ℂ),v) δ, 0<p.2.1.im ∧ p.2.2≠0) ∧
      ∀ q∈Icc (-Real.pi) Real.pi,
      AnalyticOnNhd ℂ (fun p => independentRoot b p q) (ball ((0:ℂ),v) δ) ∧
      (∀ p∈ball ((0:ℂ),v) δ, ‖independentRoot b p q‖≤2) ∧
      ∀ p∈ball ((0:ℂ),v) δ, 0<p.1.im → c*(p.1.im+q^2)≤1-‖independentRoot b p q‖ := by
  let V : Set (ℂ × ℂ) := {v | 0<v.1.im ∧ v.2≠0}
  have hV : IsOpen V := (isOpen_lt continuous_const
    (Complex.continuous_im.comp continuous_fst)).inter (isOpen_ne_fun continuous_snd continuous_const)
  obtain ⟨η,hη,hηV⟩ := hK.exists_cthickening_subset_open hV (fun v hv => ⟨hB v hv,hS v hv⟩)
  let L := cthickening η K
  have hL : IsCompact L := hK.cthickening
  obtain ⟨β,hβ,hβL⟩ : ∃ β : ℝ, 0<β ∧ ∀ v∈L, β≤v.1.im := by
    by_cases hn : L.Nonempty
    · obtain ⟨v,hv,hm⟩ := hL.exists_isMinOn hn (Complex.continuous_im.comp continuous_fst).continuousOn
      exact ⟨v.1.im,(hηV hv).1,hm⟩
    · exact ⟨1,by norm_num,fun v hv => (hn ⟨v,hv⟩).elim⟩
  obtain ⟨M,hM⟩ := hL.exists_bound_of_continuousOn continuous_fst.continuousOn
  let M' := max M 0
  have hM' : 0≤M' := le_max_right _ _
  have hBn : ∀ v∈L, ‖v.1‖≤M' := fun v hv => (hM v hv).trans (le_max_left _ _)
  have hLK : IsCompact (Prod.fst '' L) := hL.image continuous_fst
  have hLi : ∀ B∈Prod.fst '' L, 0<B.im := by rintro B ⟨v,hv,rfl⟩; exact (hηV hv).1
  obtain ⟨δ₁,r,C,hδ₁,_,_,_,hroot⟩ := compact_parameter_disk hb hLK hLi
  obtain ⟨δ₂,hδ₂,hbound⟩ := compact_root_disk hb hLK hLi
  let δ := min η (min 1 (min δ₁ δ₂))
  have hδ : 0<δ := lt_min hη (lt_min (by norm_num) (lt_min hδ₁ hδ₂))
  let c := min 1 (2*β/Real.pi^2)/(2*(|b|+1+2*M')+1)
  have hc : 0<c := by dsimp [c]; positivity
  have hp (v : ℂ × ℂ) (hv : v∈K) (p : NumeratorParameter) (hp : p∈ball ((0:ℂ),v) δ) :
      p.2∈L ∧ ‖p.1‖<1 ∧ ‖p.1‖<δ₁ ∧ ‖p.1‖<δ₂ := by
    have hh : ‖p.1‖<δ ∧ dist p.2 v<δ := by
      simpa only [mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right] using hp
    refine ⟨mem_cthickening_of_dist_le p.2 v η K hv
      (hh.2.le.trans (min_le_left _ _)),?_,?_,?_⟩
    · exact hh.1.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    · exact hh.1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    · exact hh.1.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,c,hδ,hc,?_⟩
  intro v hv
  refine ⟨fun p hp' => hηV (hp v hv p hp').1,?_⟩
  intro q hq
  refine ⟨?_,?_,?_⟩
  · intro p hp'
    have hh := hp v hv p hp'
    exact (root_analyticAt ((hroot p.1 p.2.1 hh.2.2.1 ⟨p.2,hh.1,rfl⟩).1 q hq)).comp
      (f := fun p : NumeratorParameter => (p.1,p.2.1))
      (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd))
  · intro p hp'
    have hh := hp v hv p hp'
    exact hbound p.1 p.2.1 hh.2.2.2 ⟨p.2,hh.1,rfl⟩ q hq
  · intro p hp' hi
    have hh := hp v hv p hp'
    exact root_gap_of_margins b hβ (hβL p.2 hh.1) hM' (hBn p.2 hh.1) hh.2.1.le hi hq

/-- The radius and the root-gap constant are independent of the derivative
order; only the geometric derivative constant depends on that order. -/
theorem compact_roots_geometric_mixed_jets {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ c : ℝ, 0<δ ∧ 0<c ∧ ∀ J : ℕ, ∃ M : ℝ, 1≤M ∧
      ∀ v∈K, ∀ p∈ball ((0:ℂ),v) δ, 0<p.1.im →
      (0<p.2.1.im ∧ p.2.2≠0) ∧ ∀ q∈Icc (-Real.pi) Real.pi,
      AnalyticAt ℂ (fun p => independentRoot b p q) p ∧
      (∀ k≤J, ‖iteratedFDeriv ℂ k (fun p => independentRoot b p q) p‖≤M^k) ∧
      c*(p.1.im+q^2)≤1-‖independentRoot b p q‖ := by
  obtain ⟨δ,c,hδ,hc,hall⟩ := compact_roots_polydisks hb hK hB hS
  refine ⟨δ/2,c,half_pos hδ,hc,?_⟩
  intro J
  let H := fun k : ℕ => 2/(δ/(2*((k+1:ℕ):ℝ)))^k
  let M := 1+∑ k∈Finset.range (J+1), H k
  have hH (k : ℕ) : 0≤H k := by dsimp [H]; positivity
  have hM : 1≤M := by dsimp [M]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hH k)
  refine ⟨M,hM,?_⟩
  intro v hv p hp hi
  have hp' : p∈ball ((0:ℂ),v) δ := ball_subset_ball (by linarith : δ/2≤δ) hp
  refine ⟨(hall v hv).1 p hp',?_⟩
  intro q hq
  have hh := (hall v hv).2 q hq
  have hg := hh.2.2 p hp' hi
  refine ⟨hh.1 p hp',?_,hg⟩
  intro k hk
  by_cases hk0 : k=0
  · subst k
    have hn : 0≤c*(p.1.im+q^2) := by positivity
    simpa using (show ‖independentRoot b p q‖≤1 by linarith)
  · have hsum := Finset.single_le_sum (fun i (_ : i∈Finset.range (J+1)) => hH i)
      (show k∈Finset.range (J+1) from Finset.mem_range.mpr (by omega))
    have hle : H k≤M := by dsimp [M]; linarith
    have hj := norm_iteratedFDeriv_le_on_half_ball k hδ (by norm_num : (0:ℝ)≤2) hh.1 hh.2.1 hp
    exact hj.trans (hle.trans (by simpa using pow_le_pow_right₀ hM (show 1≤k by omega)))

end
end IsingBulk.Joint.RegularEdges
