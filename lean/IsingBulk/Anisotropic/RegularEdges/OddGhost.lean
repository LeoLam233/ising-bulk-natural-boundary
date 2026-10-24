import IsingBulk.HT.First.OddSchur

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Filter IsingBulk.Schur
open scoped Topology

/-- The front ghost form is proved by a pole-free limit, so the ghost's
zero displayed diagonal denominator is never used as a hypothesis. -/
theorem schur_odd_front_norm (n : ℕ) (xs : List ℂ)
    (hlen : xs.length=2*n+1)
    (hd : ∀ v ∈ xs, ∀ w ∈ xs, 1-v*w≠0)
    (hg : ∀ v ∈ xs, v≠-1) :
    ‖pfaffian (fun a b => (a-b)/(1-a*b)) (n+1) ((-1)::xs)‖ =
      ‖pairProduct (fun a b => (a-b)/(1-a*b)) xs‖ := by
  let K : ℂ → ℂ → ℂ := fun a b => (a-b)/(1-a*b)
  let fs : List (ℂ → ℂ) := id :: (xs.map fun v => fun _ => v)
  have hmap (t : ℂ) : fs.map (fun f => f t)=t::xs := by
    simp [fs,List.map_map,Function.comp_def]
  have hden (v : ℂ) (hv : v ∈ xs) : 1-v*(-1)≠0 := by
    have hh := sub_ne_zero.mpr (hg v hv)
    simpa [add_comm] using hh
  have hc : ∀ f ∈ fs, ∀ g ∈ fs,
      ContinuousAt (fun t => K (f t) (g t)) (-1) := by
    intro f hf g hgg
    rcases List.mem_cons.mp hf with rfl | hf
    · rcases List.mem_cons.mp hgg with rfl | hgg
      · simpa [K] using (continuousAt_const : ContinuousAt (fun _ : ℂ => (0:ℂ)) (-1))
      · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hgg
        exact (continuousAt_id.sub continuousAt_const).div
          (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
          (by change 1-(-1:ℂ)*v≠0; rw [mul_comm (-1) v]; exact hden v hv)
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hf
      rcases List.mem_cons.mp hgg with rfl | hgg
      · exact (continuousAt_const.sub continuousAt_id).div
          (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)) (hden v hv)
      · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hgg
        exact continuousAt_const
  have hpf : Tendsto (fun t => pfaffian K (n+1) (fs.map (fun f => f t)))
      (𝓝[≠] (-1:ℂ)) (𝓝 (pfaffian K (n+1) (fs.map (fun f => f (-1))))) :=
    (continuousAt_pfaffian K (n+1) fs (-1) hc).mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun t => pairProduct K (fs.map (fun f => f t)))
      (𝓝[≠] (-1:ℂ)) (𝓝 (pairProduct K (fs.map (fun f => f (-1))))) :=
    (continuousAt_pairProduct K fs (-1) hc).mono_left nhdsWithin_le_nhds
  have hcross : ∀ᶠ t in 𝓝 (-1:ℂ), ∀ v ∈ xs, 1-v*t≠0 := by
    have haux : ∀ ys : List ℂ, (∀ v ∈ ys, 1-v*(-1)≠0) →
        ∀ᶠ t in 𝓝 (-1:ℂ), ∀ v ∈ ys, 1-v*t≠0 := by
      intro ys
      induction ys with
      | nil => exact fun _ => Filter.Eventually.of_forall (by simp)
      | cons v ys ih =>
        intro hh
        have hv := (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).eventually_ne
          (hh v (by simp))
        have ht := ih (fun w hw => hh w (by simp [hw]))
        filter_upwards [hv,ht] with t hvt hys w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hvt
        · exact hys w hw
    exact haux xs hden
  have hnotone : ∀ᶠ t in 𝓝 (-1:ℂ), t≠1 := continuousAt_id.eventually_ne (by norm_num)
  have heq : (fun t => pfaffian K (n+1) (fs.map (fun f => f t)))
      =ᶠ[𝓝[≠] (-1:ℂ)] (fun t => pairProduct K (fs.map (fun f => f t))) := by
    filter_upwards [hcross.filter_mono nhdsWithin_le_nhds,
      hnotone.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t hct ht1 htm
    simp only [hmap]
    apply IsingBulk.HT.First.schur_even_list
    · simp only [List.length_cons,hlen]; omega
    · intro v hv w hw
      rcases List.mem_cons.mp hv with hvt | hv
      · subst v
        rcases List.mem_cons.mp hw with hwt | hw
        · subst w
          have ha : 1-t≠0 := sub_ne_zero.mpr ht1.symm
          have hb : 1+t≠0 := by
            intro hh
            apply htm
            change t=-1
            linear_combination hh
          intro hh
          apply mul_ne_zero ha hb
          linear_combination hh
        · simpa only [mul_comm] using hct w hw
      · rcases List.mem_cons.mp hw with hwt | hw
        · subst w
          exact hct v hv
        · exact hd v hv w hw
  have he := tendsto_nhds_unique_of_eventuallyEq hpf hprod heq
  simp only [hmap] at he
  change ‖pfaffian K (n+1) ((-1)::xs)‖=‖pairProduct K xs‖
  rw [he,pairProduct,norm_mul]
  have hm : xs.map (K (-1)) = xs.map (fun _ => (-1:ℂ)) := by
    apply List.map_congr_left
    intro v hv
    have hh := IsingBulk.HT.First.schur_ghost_entry (hg v hv)
    change ((-1:ℂ)-v)/(1-(-1)*v) = -1
    have hs : ((-1:ℂ)-v)/(1-(-1)*v) = -((v-(-1))/(1-v*(-1))) := by ring
    rw [hs,hh]
  rw [hm]
  simp
end
end IsingBulk.Anisotropic.RegularEdges
