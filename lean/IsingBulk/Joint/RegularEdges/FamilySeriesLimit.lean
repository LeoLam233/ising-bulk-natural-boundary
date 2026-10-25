import IsingBulk.Joint.RegularEdges.FamilySeriesJets
import IsingBulk.Joint.RegularEdges.UniformNoncancellation

/-! # Uniform first-singularity selection in the complete parity series -/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators

theorem uniform_complex_add {E A : Type*} {Q : Set E} {l : Filter A}
    {F G : A→E→ℂ} {f g : E→ℂ}
    (hf : TendstoUniformlyOn F f l Q) (hg : TendstoUniformlyOn G g l Q) :
    TendstoUniformlyOn (fun t eta=>F t eta+G t eta) (fun eta=>f eta+g eta) l Q := by
  rw [Metric.tendstoUniformlyOn_iff] at hf hg ⊢
  intro ε hε
  filter_upwards [hf (ε/2) (half_pos hε),hg (ε/2) (half_pos hε)] with t ht ht'
  intro eta heta
  exact (dist_add_add_le _ _ _ _).trans_lt (by linarith [ht eta heta,ht' eta heta])

theorem uniform_complex_finset_sum {E A I : Type*} {Q : Set E} {l : Filter A}
    (s : Finset I) {F : I→A→E→ℂ} {f : I→E→ℂ}
    (hf : ∀i∈s,TendstoUniformlyOn (F i) (f i) l Q) :
    TendstoUniformlyOn (fun t eta=>∑i∈s,F i t eta) (fun eta=>∑i∈s,f i eta) l Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (tendsto_const_nhds : Tendsto (fun _ : A=>(0:ℂ)) l (𝓝 0)).tendstoUniformlyOn_const Q
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using uniform_complex_add (hf i (Finset.mem_insert_self _ _))
        (ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj)))

theorem uniform_bounded_scaled_zero {E : Type*} {Q : Set E} {F : ℝ→E→ℂ}
    {a : ℕ} (ha : 0<a) {D : ℝ}
    (hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,‖F t eta‖≤D) :
    TendstoUniformlyOn (fun t eta=>(t^a) • F t eta) (fun _=>0) (𝓝[>] (0:ℝ)) Q := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun t : ℝ=>t^a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id_eq,zero_pow (Nat.ne_of_gt ha)] using
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ=>t) (𝓝[>] 0) (𝓝 0)).pow a
  have hp := ht.eventually (eventually_lt_nhds (div_pos hε (show 0<max D 0+1 by positivity)))
  filter_upwards [hbound,hp,self_mem_nhdsWithin] with t hb hp htpos
  intro eta heta
  rw [dist_zero_left,norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos htpos a)]
  calc
    _ ≤ t^a*(max D 0+1) := mul_le_mul_of_nonneg_left
      ((hb eta heta).trans (by linarith [le_max_left D 0])) (pow_nonneg htpos.le a)
    _ < ε := (lt_div_iff₀ (by positivity)).mp hp

/-- The finite prefix is controlled uniformly term by term, while the entire
infinite tail uses one summable envelope. All limits refer to the actual sum. -/
theorem uniform_scaled_series_first_limit {E : Type*} {Q : Set E}
    {a L p : ℕ} (ha : 0<a) (hp : p<L)
    {f : ℕ→ℝ→E→ℂ} {F : ℝ→E→ℂ} {C : E→ℂ}
    (hs : ∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,HasSum (fun n=>f n t eta) (F t eta))
    (hfirst : ∀n<L,TendstoUniformlyOn (fun t eta=>(t^a) • f n t eta)
      (fun eta=>if n=p then C eta else 0) (𝓝[>] (0:ℝ)) Q)
    {G : ℕ→ℝ} (hG : Summable G)
    (htail : ∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,∀n,‖f (n+L) t eta‖≤G n) :
    TendstoUniformlyOn (fun t eta=>(t^a) • F t eta) C (𝓝[>] (0:ℝ)) Q := by
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,∀eta∈Q,‖∑'n,f (n+L) t eta‖≤∑'n,G n := by
    filter_upwards [htail] with t ht
    intro eta heta
    have hn := hG.of_nonneg_of_le (fun _=>norm_nonneg _) (ht eta heta)
    exact (norm_tsum_le_tsum_norm hn).trans (Summable.tsum_le_tsum (ht eta heta) hn hG)
  have hzero := uniform_bounded_scaled_zero ha hb
  have hfinite := uniform_complex_finset_sum (Finset.range L)
    (fun n hn=>hfirst n (Finset.mem_range.mp hn))
  simp only [Finset.sum_ite_eq',Finset.mem_range,hp,ite_true] at hfinite
  have hh := uniform_complex_add hfinite hzero
  simp only [add_zero] at hh
  apply hh.congr
  filter_upwards [hs] with t ht
  intro eta heta
  dsimp only
  rw [←(ht eta heta).tsum_eq,←(ht eta heta).summable.sum_add_tsum_nat_add L,
    smul_add,Finset.smul_sum]

end
end IsingBulk.Joint.RegularEdges
