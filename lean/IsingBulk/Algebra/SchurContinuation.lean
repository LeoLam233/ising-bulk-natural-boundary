import IsingBulk.Algebra.SchurMobius
import Mathlib.Topology.Algebra.Monoid

/-! Specialization on a pole-free chart, including coincident variable values. -/
namespace IsingBulk.Schur
noncomputable section
open Filter
open scoped Topology

theorem continuousAt_pairProduct {T : Type*} [TopologicalSpace T]
    (K : ℂ → ℂ → ℂ) (fs : List (T → ℂ)) (t : T)
    (h : ∀ f ∈ fs, ∀ g ∈ fs, ContinuousAt (fun u => K (f u) (g u)) t) :
    ContinuousAt (fun u => pairProduct K (fs.map (fun f => f u))) t := by
  induction fs with
  | nil => simpa [pairProduct] using (continuousAt_const : ContinuousAt (fun _ : T => (1 : ℂ)) t)
  | cons f fs ih =>
    simp only [List.map_cons, pairProduct, List.map_map, Function.comp_def]
    exact (tendsto_list_prod fs (fun g hg => h f (by simp) g (by simp [hg]))).mul
      (ih (fun g hg k hk => h g (by simp [hg]) k (by simp [hk])))

theorem continuousAt_pfaffian {T : Type*} [TopologicalSpace T]
    (K : ℂ → ℂ → ℂ) (n : ℕ) (fs : List (T → ℂ)) (t : T)
    (h : ∀ f ∈ fs, ∀ g ∈ fs, ContinuousAt (fun u => K (f u) (g u)) t) :
    ContinuousAt (fun u => pfaffian K n (fs.map (fun f => f u))) t := by
  induction n generalizing fs with
  | zero => simpa [pfaffian] using (continuousAt_const : ContinuousAt (fun _ : T => (1 : ℂ)) t)
  | succ n ih =>
    cases fs with
    | nil => simpa [pfaffian] using (continuousAt_const : ContinuousAt (fun _ : T => (0 : ℂ)) t)
    | cons f fs =>
      simp only [List.map_cons, pfaffian, List.zipIdx_map, List.map_map,
        List.eraseIdx_map, Function.comp_def]
      apply tendsto_list_sum fs.zipIdx
      rintro ⟨g,j⟩ hgj
      have hg : g ∈ fs := by
        rw [(List.mem_zipIdx' hgj).2]
        exact List.getElem_mem (List.mem_zipIdx' hgj).1
      have hfirst : ContinuousAt (fun u => (-1 : ℂ)^j * K (f u) (g u)) t :=
        (continuousAt_const : ContinuousAt (fun _ : T => (-1 : ℂ)^j) t).mul
          (h f (by simp) g (by simp [hg]))
      have hlast : ContinuousAt (fun u => pfaffian K n ((fs.eraseIdx j).map (fun f => f u))) t :=
        ih _ (fun k hk l hl =>
          h k (List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx hk))
            l (List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx hl)))
      exact hfirst.mul hlast

def perturb {m : ℕ} (v : Fin m → ℂ) (i : Fin m) (t : ℂ) : ℂ := v i + (i.val : ℂ)*t

theorem perturb_continuous {m : ℕ} (v : Fin m → ℂ) (i : Fin m) : Continuous (perturb v i) :=
  continuous_const.add (continuous_const.mul continuous_id)

theorem perturb_eventually_injective {m : ℕ} (v : Fin m → ℂ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), Function.Injective (fun i => perturb v i t) := by
  have he : ∀ i j : Fin m, ∀ᶠ t in 𝓝[≠] (0 : ℂ), i ≠ j → perturb v i t ≠ perturb v j t := by
    intro i j
    by_cases hij : v i = v j
    · filter_upwards [self_mem_nhdsWithin] with t ht hne hh
      have ht0 : t ≠ 0 := ht
      have hh' : ((i.val : ℂ) - (j.val : ℂ))*t = 0 := by
        unfold perturb at hh
        rw [hij] at hh
        linear_combination hh
      have hc := sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_right ht0)
      exact hne (Fin.ext (by exact_mod_cast hc))
    · have hdiff : ContinuousAt (fun t => perturb v i t - perturb v j t) (0 : ℂ) :=
        (perturb_continuous v i).continuousAt.sub (perturb_continuous v j).continuousAt
      have hc : ∀ᶠ t in 𝓝 (0 : ℂ), perturb v i t - perturb v j t ≠ 0 :=
        hdiff.eventually_ne (by simpa [perturb] using sub_ne_zero.mpr hij)
      filter_upwards [hc.filter_mono nhdsWithin_le_nhds] with t ht _
      exact sub_ne_zero.mp ht
  have hall := Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (he i))
  filter_upwards [hall] with t ht i j hij
  by_contra hne
  exact ht i j hne hij

/-- Pointwise specialization on the chart with all pair denominators nonzero,
including diagonal denominators. Coincident variables are allowed.
The diagonal condition is automatic on the manuscript's strict subdisk. -/
theorem schur_fraction_specialization (n : ℕ) (v : Fin (2*n) → ℂ)
    (hd : ∀ i j, 1-v i*v j ≠ 0) :
    pfaffian (fun a b => (a-b)/(1-a*b)) n (List.ofFn v) =
      pairProduct (fun a b => (a-b)/(1-a*b)) (List.ofFn v) := by
  let fs := List.ofFn (perturb v)
  let K : ℂ → ℂ → ℂ := fun a b => (a-b)/(1-a*b)
  have hc : ∀ f ∈ fs, ∀ g ∈ fs, ContinuousAt (fun t => K (f t) (g t)) 0 := by
    intro f hf g hg
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact ((perturb_continuous v i).continuousAt.sub (perturb_continuous v j).continuousAt).div
      (continuousAt_const.sub ((perturb_continuous v i).continuousAt.mul (perturb_continuous v j).continuousAt))
      (by simpa [perturb] using hd i j)
  have hP : Tendsto (fun t => pfaffian K n (fs.map (fun f => f t))) (𝓝[≠] (0 : ℂ))
      (𝓝 (pfaffian K n (fs.map (fun f => f 0)))) :=
    (continuousAt_pfaffian K n fs 0 hc).mono_left nhdsWithin_le_nhds
  have hV : Tendsto (fun t => pairProduct K (fs.map (fun f => f t))) (𝓝[≠] (0 : ℂ))
      (𝓝 (pairProduct K (fs.map (fun f => f 0)))) :=
    (continuousAt_pairProduct K fs 0 hc).mono_left nhdsWithin_le_nhds
  have hden : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i j, 1-perturb v i t * perturb v j t ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (continuousAt_const.sub ((perturb_continuous v i).continuousAt.mul
      (perturb_continuous v j).continuousAt)).eventually_ne (by simpa [perturb] using hd i j)
  have heq : (fun t => pfaffian K n (fs.map (fun f => f t))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun t => pairProduct K (fs.map (fun f => f t))) := by
    filter_upwards [perturb_eventually_injective v, hden.filter_mono nhdsWithin_le_nhds] with t hinj hdt
    have hmap : fs.map (fun f => f t) = List.ofFn (fun i => perturb v i t) := by
      simp only [fs, List.map_ofFn, Function.comp_def]
    rw [hmap]
    apply schur_fraction_of_nodup n _ (by simp) (List.nodup_ofFn.mpr hinj)
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      intro hi
      exact hdt i i (by rw [hi]; norm_num)
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      intro hi
      exact hdt i i (by rw [hi]; norm_num)
    · intro z hz w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      exact hdt i j
  have h := tendsto_nhds_unique_of_eventuallyEq hP hV heq
  simpa only [fs, List.map_ofFn, Function.comp_def, perturb, mul_zero, add_zero, K] using h

theorem schur_subdisk (n : ℕ) (v : Fin (2*n) → ℂ) (hv : ∀ i, ‖v i‖ < 1) :
    pfaffian (fun a b => (a-b)/(1-a*b)) n (List.ofFn v) =
      pairProduct (fun a b => (a-b)/(1-a*b)) (List.ofFn v) :=
  schur_fraction_specialization n v (fun i j => denominator_ne_zero (hv i) (hv j))

theorem schur_compact_exterior (n : ℕ) (v : Fin (2*n) → ℂ) {r : ℝ}
    (hr : r < 1) (hv : ∀ i, ‖v i‖ ≤ r) :
    pfaffian (fun a b => (a-b)/(1-a*b)) n (List.ofFn v) =
      pairProduct (fun a b => (a-b)/(1-a*b)) (List.ofFn v) :=
  schur_subdisk n v (fun i => (hv i).trans_lt hr)

/-- The two Pfaffians in Appendix C: contour variables have modulus r,
and interior dispersion roots have modulus at most q, with q < r < 1. -/
theorem schur_appendix_C (n : ℕ) (y z : Fin (2*n) → ℂ) {q r : ℝ}
    (hqr : q < r) (hr : r < 1) (hy : ∀ i, ‖y i‖ = r) (hz : ∀ i, ‖z i‖ ≤ q) :
    (pfaffian (fun a b => (a-b)/(1-a*b)) n (List.ofFn y) =
      pairProduct (fun a b => (a-b)/(1-a*b)) (List.ofFn y)) ∧
    (pfaffian (fun a b => (a-b)/(1-a*b)) n (List.ofFn z) =
      pairProduct (fun a b => (a-b)/(1-a*b)) (List.ofFn z)) :=
  ⟨schur_subdisk n y (fun i => (hy i).trans_lt hr),
    schur_subdisk n z (fun i => (hz i).trans_lt (hqr.trans hr))⟩

end
end IsingBulk.Schur
