import IsingBulk.Algebra.SchurContinuation

/-!
HT-1.0, Lemma `lem:schur`: the odd-particle ghost extension.

The existing even specialization assumes nonzero diagonal denominators. At the
new ghost value -1 that condition fails. We therefore take a pole-free limit in
the ghost variable. The ghost/ghost entry is identically zero and is continuous,
although its displayed denominator vanishes at the limit. No LT module changes.
-/
namespace IsingBulk.HT.First
noncomputable section
open Filter IsingBulk.Schur
open scoped Topology

/-- List-facing adapter to the established even Schur specialization. -/
theorem schur_even_list (n : ℕ) (xs : List ℂ) (hlen : xs.length = 2*n)
    (hd : ∀ v ∈ xs, ∀ w ∈ xs, 1-v*w ≠ 0) :
    pfaffian (fun a b => (a-b)/(1-a*b)) n xs =
      pairProduct (fun a b => (a-b)/(1-a*b)) xs := by
  have hfinite : ∀ m : ℕ, ∀ v : Fin m → ℂ, m = 2*n →
      (∀ i j, 1-v i*v j ≠ 0) →
      pfaffian (fun a b => (a-b)/(1-a*b)) n (List.ofFn v) =
        pairProduct (fun a b => (a-b)/(1-a*b)) (List.ofFn v) := by
    intro m v hm h
    subst m
    exact schur_fraction_specialization n v h
  have h := hfinite xs.length xs.get hlen (fun i j =>
    hd _ (List.get_mem _ _) _ (List.get_mem _ _))
  simpa using h

/-- Appending a constant unit last column does not change the pair product. -/
theorem pairProduct_append_unit {R : Type*} [CommRing R]
    (K : R → R → R) (xs : List R) (g : R)
    (h : ∀ v ∈ xs, K v g = 1) :
    pairProduct K (xs ++ [g]) = pairProduct K xs := by
  induction xs with
  | nil => simp [pairProduct]
  | cons a xs ih =>
    simp only [List.cons_append, pairProduct, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [h a (by simp), mul_one, ih (fun v hv => h v (by simp [hv]))]

/-- The last upper ghost entry is one whenever the physical variable is not -1. -/
theorem schur_ghost_entry {v : ℂ} (hv : v ≠ -1) :
    (v-(-1))/(1-v*(-1)) = 1 := by
  have h : v+1 ≠ 0 := by simpa using sub_ne_zero.mpr hv
  simpa [add_comm] using div_self h

private theorem ghost_denominator {v : ℂ} (hv : v ≠ -1) :
    1-v*(-1) ≠ 0 := by
  have h : v+1 ≠ 0 := by simpa using sub_ne_zero.mpr hv
  simpa [add_comm] using h

/-- The full odd identity, valid for deformed contours as well as subdisks.
Only physical/physical denominators and physical/ghost entries are required;
the ghost's zero diagonal denominator is deliberately not an assumption. -/
theorem schur_odd_specialization (n : ℕ) (xs : List ℂ)
    (hlen : xs.length = 2*n+1)
    (hd : ∀ v ∈ xs, ∀ w ∈ xs, 1-v*w ≠ 0)
    (hg : ∀ v ∈ xs, v ≠ -1) :
    pfaffian (fun a b => (a-b)/(1-a*b)) (n+1) (xs ++ [-1]) =
      pairProduct (fun a b => (a-b)/(1-a*b)) xs := by
  let K : ℂ → ℂ → ℂ := fun a b => (a-b)/(1-a*b)
  let fs : List (ℂ → ℂ) := (xs.map fun v => fun _ => v) ++ [id]
  have hmap (t : ℂ) : fs.map (fun f => f t) = xs ++ [t] := by
    simp [fs, List.map_map, Function.comp_def]
  have hcontinuous : ∀ f ∈ fs, ∀ g ∈ fs,
      ContinuousAt (fun t => K (f t) (g t)) (-1) := by
    intro f hf g hg'
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hf
      rcases List.mem_append.mp hg' with hgg | hgg
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hgg
        exact continuousAt_const
      · have hg' : g = id := by simpa using hgg
        subst g
        exact (continuousAt_const.sub continuousAt_id).div
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
          (ghost_denominator (hg v hv))
    · have hf' : f = id := by simpa using hf
      subst f
      rcases List.mem_append.mp hg' with hgg | hgg
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hgg
        exact (continuousAt_id.sub continuousAt_const).div
          (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
          (by
            change 1-(-1:ℂ)*v ≠ 0
            rw [mul_comm (-1) v]
            exact ghost_denominator (hg v hv))
      · have hg' : g = id := by simpa using hgg
        subst g
        simpa [K] using
          (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) (-1))
  have hpf : Tendsto (fun t => pfaffian K (n+1) (fs.map (fun f => f t)))
      (𝓝[≠] (-1 : ℂ)) (𝓝 (pfaffian K (n+1) (fs.map (fun f => f (-1))))) :=
    (continuousAt_pfaffian K (n+1) fs (-1) hcontinuous).mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun t => pairProduct K (fs.map (fun f => f t)))
      (𝓝[≠] (-1 : ℂ)) (𝓝 (pairProduct K (fs.map (fun f => f (-1))))) :=
    (continuousAt_pairProduct K fs (-1) hcontinuous).mono_left nhdsWithin_le_nhds
  have hcross : ∀ᶠ t in 𝓝 (-1 : ℂ), ∀ v ∈ xs, 1-v*t ≠ 0 := by
    have hfinite : ∀ ys : List ℂ,
        (∀ v ∈ ys, v ≠ -1) →
        ∀ᶠ t in 𝓝 (-1 : ℂ), ∀ v ∈ ys, 1-v*t ≠ 0 := by
      intro ys
      induction ys with
      | nil => exact fun _ => Filter.Eventually.of_forall (by simp)
      | cons v ys ih =>
        intro hm
        have hc := (continuousAt_const.sub
          (continuousAt_const.mul continuousAt_id)).eventually_ne
            (ghost_denominator (hm v (by simp)))
        have ht := ih (fun w hw => hm w (by simp [hw]))
        filter_upwards [hc,ht] with t hvt hys w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hvt
        · exact hys w hw
    exact hfinite xs hg
  have hnotone : ∀ᶠ t in 𝓝 (-1 : ℂ), t ≠ 1 :=
    continuousAt_id.eventually_ne (by norm_num)
  have heq : (fun t => pfaffian K (n+1) (fs.map (fun f => f t)))
      =ᶠ[𝓝[≠] (-1 : ℂ)]
      (fun t => pairProduct K (fs.map (fun f => f t))) := by
    filter_upwards [hcross.filter_mono nhdsWithin_le_nhds,
      hnotone.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hct ht1 htm
    simp only [hmap]
    apply schur_even_list
    · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
      omega
    · intro v hv w hw
      rcases List.mem_append.mp hv with hv | hv
      · rcases List.mem_append.mp hw with hw | hw
        · exact hd v hv w hw
        · have hw' : w = t := by simpa using hw
          subst w
          exact hct v hv
      · have hv' : v = t := by simpa using hv
        subst v
        rcases List.mem_append.mp hw with hw | hw
        · simpa only [mul_comm t] using hct w hw
        · have hw' : w = t := by simpa using hw
          subst w
          have ha : 1-t ≠ 0 := sub_ne_zero.mpr ht1.symm
          have hb : 1+t ≠ 0 := by
            intro hh
            apply htm
            change t = -1
            linear_combination hh
          intro hh
          apply mul_ne_zero ha hb
          linear_combination hh
  have he := tendsto_nhds_unique_of_eventuallyEq hpf hprod heq
  simp only [hmap] at he
  rw [pairProduct_append_unit K xs (-1) (fun v hv => schur_ghost_entry (hg v hv))] at he
  exact he

/-- Original interior contours satisfy all physical and ghost hypotheses. -/
theorem schur_odd_subdisk (n : ℕ) (xs : List ℂ)
    (hlen : xs.length = 2*n+1) (hv : ∀ v ∈ xs, ‖v‖ < 1) :
    pfaffian (fun a b => (a-b)/(1-a*b)) (n+1) (xs ++ [-1]) =
      pairProduct (fun a b => (a-b)/(1-a*b)) xs := by
  apply schur_odd_specialization n xs hlen
  · exact fun v hvm w hwm => denominator_ne_zero (hv v hvm) (hv w hwm)
  · intro v hvm heq
    have h := hv v hvm
    simp [heq] at h

end
end IsingBulk.HT.First
