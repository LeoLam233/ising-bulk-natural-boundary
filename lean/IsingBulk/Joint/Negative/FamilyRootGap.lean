import IsingBulk.Joint.RegularEdges.CompactRootJets
import IsingBulk.Anisotropic.NegativeDominance.OddComplexGap

/-! # Uniform odd-particle gaps for compact complex families
The compact family contains both anisotropy and particle scale. All constants
are chosen before the family member, particle index and angular configuration.
-/
namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges
  IsingBulk.Anisotropic.NegativeDominance IsingBulk.Joint.RegularEdges Set Filter Metric
open scoped Topology BigOperators

theorem compact_boundary_quadratic_gap {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K) (hB : ∀ v∈K, 0<v.1.im) :
    ∃ c : ℝ, 0<c ∧ ∀ v∈K, ∀ q∈Icc (-Real.pi) Real.pi,
      c*q^2≤1-‖edgeRoot b v.1 q‖ := by
  obtain ⟨β,hβ,hβK⟩ : ∃ β : ℝ, 0<β ∧ ∀ v∈K, β≤v.1.im := by
    by_cases hn : K.Nonempty
    · obtain ⟨v,hv,hm⟩ := hK.exists_isMinOn hn
        (Complex.continuous_im.comp continuous_fst).continuousOn
      exact ⟨v.1.im,hB v hv,hm⟩
    · exact ⟨1,by norm_num,fun v hv => (hn ⟨v,hv⟩).elim⟩
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_fst.continuousOn
  let W := |b|+1+2*max M 0
  let k := 2*β/Real.pi^2
  have hW : 0<W := by dsimp [W]; positivity
  have hk : 0<k := by dsimp [k]; positivity
  refine ⟨k/(2*W+1),by positivity,?_⟩
  intro v hv q hq
  by_cases hq0 : q=0
  · rw [hq0,pow_two,zero_mul,mul_zero]
    linarith [(edgeRoot_bounds hb (hB v hv) 0).1]
  have hm : k*q^2≤(edgeW b v.1 q).im := by
    have hh := edgeParamW_im_margin (B := fun _ => v.1) (u := (0 : ℂ))
      b hβ.le (hβK v hv) (abs_le.mpr hq)
    simpa only [k,edgeParamW,edgeW,add_zero,Complex.zero_im,zero_add] using hh
  have hw : 0<(edgeW b v.1 q).im := lt_of_lt_of_le (mul_pos hk (sq_pos_of_ne_zero hq0)) hm
  have hn : ‖edgeW b v.1 q‖≤W := by
    have hh := edgeParamW_norm_bound (B := fun _ => v.1) (u := (0 : ℂ)) b
      (by simp) ((hM v hv).trans (le_max_left M 0)) q
    simpa only [W,edgeParamW,edgeW,add_zero] using hh
  rw [edgeRoot,continuedRoot_eq_interiorRoot hw]
  calc
    k/(2*W+1)*q^2 = (k*q^2)/(2*W+1) := by ring
    _ ≤ (edgeW b v.1 q).im/(2*W+1) := div_le_div_of_nonneg_right hm (by positivity)
    _ ≤ _ := interiorRoot_modulus_gap hw hn

theorem compact_odd_boundary_product_gap {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K) (hB : ∀ v∈K, 0<v.1.im) :
    ∃ c : ℝ, 0<c ∧ ∀ w∈K, ∀ (n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ,
      c/((n+1 : ℕ) : ℝ)^2≤1-‖∏ i,edgeRoot b w.1 (negativeShiftedAngles n v i)‖ := by
  obtain ⟨c,hc,hgap⟩ := compact_boundary_quadratic_gap hb hK hB
  refine ⟨4*c,by positivity,?_⟩
  intro w hw n hn v
  let q := negativeShiftedAngles n v
  have hr (i : Fin (n+1)) : ‖edgeRoot b w.1 (q i)‖≤1 := (edgeRoot_bounds hb (hB w hw) _).1
  obtain ⟨i,hi⟩ := (IsGreatest.pi_norm q).1
  have hsq : (q i)^2=‖q‖^2 := by
    rw [←hi]
    change (q i)^2=‖q i‖^2
    simp only [Real.norm_eq_abs,sq_abs]
  have hg := hgap w hw (q i) (wrapAngle_mem _)
  rw [hsq] at hg
  have hprod := root_product_norm_le_factor (fun i => edgeRoot b w.1 (q i)) hr i
  have htotal : c*‖q‖^2≤1-‖∏ i,edgeRoot b w.1 (q i)‖ := by linarith
  have hm := odd_shifted_angles_norm_lower hn v
  have hm2 : 4≤((n+1 : ℕ) : ℝ)^2*‖q‖^2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤2) hm 2
    simpa only [mul_pow,show (2 : ℝ)^2=4 by norm_num] using hh
  have hN : 0<((n+1 : ℕ) : ℝ)^2 := by positivity
  apply (div_le_iff₀ hN).mpr
  have h1 := mul_le_mul_of_nonneg_left hm2 hc.le
  have h2 := mul_le_mul_of_nonneg_left htotal hN.le
  nlinarith

theorem compact_root_lipschitz {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧ ∀ v∈K, ∀ p∈ball ((0:ℂ),v) δ,
      ∀ q∈Icc (-Real.pi) Real.pi,
      AnalyticAt ℂ (fun p => independentRoot b p q) p ∧
      ‖independentRoot b p q-independentRoot b (0,v) q‖≤L*‖p-(0,v)‖ := by
  obtain ⟨δ,c,hδ,_hc,hall⟩ := compact_roots_polydisks hb hK hB hS
  refine ⟨δ/2,8/δ,half_pos hδ,by positivity,?_⟩
  intro v hv p hp q hq
  have hh := (hall v hv).2 q hq
  have hsub : ball ((0:ℂ),v) (δ/2)⊆ball ((0:ℂ),v) δ := ball_subset_ball (by linarith)
  refine ⟨hh.1 p (hsub hp),?_⟩
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (hh.1 x (hsub hx)).differentiableAt) ?_
    (convex_ball ((0:ℂ),v) (δ/2)) (mem_ball_self (half_pos hδ)) hp
  intro x hx
  have hj := norm_iteratedFDeriv_le_on_half_ball 1 hδ (by norm_num : (0:ℝ)≤2) hh.1 hh.2.1 hx
  rw [norm_iteratedFDeriv_one] at hj
  convert hj using 1
  norm_num
  ring


/-- The odd full product retains a uniform polynomial gap throughout a genuine
independent complex polydisk, not just along real-ratio slices. -/
theorem compact_odd_complex_product_gap {b : ℝ} {K : Set (ℂ × ℂ)}
    (hb : |b|<1) (hK : IsCompact K)
    (hB : ∀ v∈K, 0<v.1.im) (hS : ∀ v∈K, v.2≠0) :
    ∃ a c : ℝ, 0<a ∧ 0<c ∧ ∀ w∈K,
      ∀ (n : ℕ), Odd (n+1) → ∀ v : Fin n → ℝ,
      ∀ p∈ball ((0:ℂ),w) (a/((n+1:ℕ):ℝ)^3),
        (∀ i, AnalyticAt ℂ (fun x => independentRoot b x (negativeShiftedAngles n v i)) p) ∧
        c/((n+1:ℕ):ℝ)^2≤1-‖∏ i, independentRoot b p (negativeShiftedAngles n v i)‖ := by
  obtain ⟨κ,hκ,hboundary⟩ := compact_odd_boundary_product_gap hb hK hB
  obtain ⟨δ,L,hδ,hL,hroot⟩ := compact_root_lipschitz hb hK hB hS
  let E := Real.exp 1
  have hE : 0<E := Real.exp_pos _
  have hE1 : 1≤E := Real.one_le_exp_iff.mpr (by norm_num)
  let a := min δ (min (1/(E*L)) (κ/(2*E*L)))
  have ha : 0<a := lt_min hδ (lt_min (by positivity) (by positivity))
  have haδ : a≤δ := min_le_left _ _
  have ha1 : a≤1/(E*L) := (min_le_right _ _).trans (min_le_left _ _)
  have haκ : a≤κ/(2*E*L) := (min_le_right _ _).trans (min_le_right _ _)
  have hELa : E*L*a≤1 := by have hh := (le_div_iff₀ (mul_pos hE hL)).mp ha1; nlinarith
  have hELκ : E*L*a≤κ/2 := by have hh := (le_div_iff₀ (by positivity : 0<2*E*L)).mp haκ; nlinarith
  refine ⟨a,κ/2,ha,by positivity,?_⟩
  intro w hw n hn v p hp
  let u := ‖p-((0:ℂ),w)‖
  have hu : u<a/((n+1:ℕ):ℝ)^3 := by simpa only [mem_ball,dist_eq_norm] using hp
  let N : ℝ := (n+1 : ℕ)
  have hN : 1≤N := by dsimp [N]; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hN0 : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hN2 : 1≤N^2 := one_le_pow₀ hN
  have hN3 : 1≤N^3 := one_le_pow₀ hN
  have hun : u<a/N^3 := hu
  have hau : a/N^3≤a := (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith)
  have huδ : u<δ := hun.trans_le (hau.trans haδ)
  have hscale : N*u≤a/N^2 := by
    calc
      N*u ≤ N*(a/N^3) := mul_le_mul_of_nonneg_left hun.le hN0.le
      _ = a/N^2 := by field_simp
  have haN2 : a/N^2≤a := (div_le_iff₀ (pow_pos hN0 _)).mpr (by nlinarith)
  have hNd : N*(L*u)≤1 := by
    have hh := mul_le_mul_of_nonneg_left (hscale.trans haN2) hL.le
    have he := mul_le_mul_of_nonneg_right hE1 (show 0≤L*a by positivity)
    nlinarith
  let q := negativeShiftedAngles n v
  have hbase (i : Fin (n+1)) : ‖independentRoot b (0,w) (q i)‖≤1 := by
    simpa only [independentRoot,root_zero] using (edgeRoot_bounds hb (hB w hw) (q i)).1
  have hdif (i : Fin (n+1)) : ‖independentRoot b p (q i)-independentRoot b (0,w) (q i)‖≤L*u :=
    (hroot w hw p (by simpa only [mem_ball,dist_eq_norm] using huδ) (q i) (wrapAngle_mem _)).2
  have hp := norm_prod_perturbation_linear (fun i => independentRoot b p (q i))
    (fun i => independentRoot b (0,w) (q i)) (by positivity : 0≤L*u) hNd hbase hdif
  have herror : E*N*(L*u)≤κ/(2*N^2) := by
    calc
      E*N*(L*u) = E*L*(N*u) := by ring
      _ ≤ E*L*(a/N^2) := mul_le_mul_of_nonneg_left hscale (mul_pos hE hL).le
      _ = (E*L*a)/N^2 := by ring
      _ ≤ (κ/2)/N^2 := div_le_div_of_nonneg_right hELκ (sq_nonneg N)
      _ = κ/(2*N^2) := by ring
  have hgap := hboundary w hw n hn v
  have htri := norm_add_le ((∏ i,independentRoot b p (q i))-(∏ i,independentRoot b (0,w) (q i)))
    (∏ i,independentRoot b (0,w) (q i))
  rw [sub_add_cancel] at htri
  simp only [independentRoot,root_zero] at hp htri
  refine ⟨fun i => (hroot w hw p (by simpa only [mem_ball,dist_eq_norm] using huδ) (q i) (wrapAngle_mem _)).1,?_⟩
  change (κ/2)/N^2≤1-‖∏ i,independentRoot b p (q i)‖
  have heq : κ/(2*N^2)=(κ/2)/N^2 := by ring
  have heq2 : κ/N^2=2*((κ/2)/N^2) := by ring
  change κ/N^2≤1-‖∏ i,edgeRoot b w.1 (q i)‖ at hgap
  rw [heq2] at hgap
  rw [heq] at herror
  change ‖(∏ i,independentRoot b p (q i))-(∏ i,edgeRoot b w.1 (q i))‖≤E*N*(L*u) at hp
  dsimp only [independentRoot] at hp ⊢
  linarith

end
end IsingBulk.Joint.Negative
