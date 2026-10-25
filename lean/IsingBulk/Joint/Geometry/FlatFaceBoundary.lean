import IsingBulk.Joint.Transverse.LocalSide
import IsingBulk.Joint.Transverse.NegativeLocalSide

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology

def flatNormal (eps : ℝ) (q : Coupling) : ℝ := (q.1-(eps:ℂ)*q.2).im

theorem frontier_of_flat_chart {D U : Set Coupling} (hD : IsOpen D) (hU : IsOpen U)
    (e : OpenPartialHomeomorph Coupling Coupling) {eps : ℝ}
    (hside : ∀ L ∈ U, L ∈ D ↔ 0 < flatNormal eps (e L))
    {L : Coupling} (hLs : L ∈ e.source) (hLU : L ∈ U)
    (hn : flatNormal eps (e L) = 0) : L ∈ frontier D := by
  let q : ℝ → Coupling := fun t => ((e L).1+(t:ℂ)*Complex.I,(e L).2)
  have hq0 : q 0 = e L := by simp [q]
  have hq : Continuous q := by unfold q; fun_prop
  have ht : e L ∈ e.target := e.map_source hLs
  have hc : ContinuousAt (fun t => e.symm (q t)) 0 := by
    have he := e.symm.continuousAt ht
    have he' : ContinuousAt e.symm (q 0) := hq0.symm ▸ he
    exact he'.comp (hq.continuousAt (x:=0))
  have hc0 : e.symm (q 0) = L := by rw [hq0,e.left_inv hLs]
  have hevent : ∀ᶠ t : ℝ in 𝓝 0, q t ∈ e.target ∧ e.symm (q t) ∈ U := by
    have ha := (hq.continuousAt (x:=0)).preimage_mem_nhds (by simpa only [hq0] using e.open_target.mem_nhds ht)
    have hb := hc.preimage_mem_nhds (by simpa only [hc0] using hU.mem_nhds hLU)
    exact inter_mem ha hb
  have hlim : Tendsto (fun t => e.symm (q t)) (𝓝[>] 0) (𝓝 L) := by
    simpa only [hc0] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmem : ∀ᶠ t : ℝ in 𝓝[>] 0, e.symm (q t) ∈ D := by
    filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hpos
    apply (hside _ ht.2).mpr
    rw [e.right_inv ht.1]
    have he : flatNormal eps (q t) = flatNormal eps (e L)+t := by
      simp only [flatNormal,q,Complex.sub_im,Complex.add_im,Complex.mul_im,
        Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
      ring
    rw [he,hn,zero_add]
    exact hpos
  rw [hD.frontier_eq]
  refine ⟨mem_closure_of_tendsto hlim hmem,?_⟩
  intro hd
  have h := (hside L hLU).mp hd
  rw [hn] at h
  exact lt_irrefl _ h

end
end IsingBulk.Joint
