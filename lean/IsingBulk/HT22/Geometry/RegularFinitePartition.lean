import IsingBulk.HT22.Geometry.FiniteCenterCutoffs
import IsingBulk.HT22.Geometry.FiniteComplementPartition

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.Preferred22 IsingBulk.First IsingBulk.PrimeFamily Arithmetic LocalLimit
open scoped BigOperators Topology ContDiff

def regularSignedMeanIndices (d : PreferredBranchData) (B : PreferredCoareaBump d)
    (negative : Bool) (N : ℕ) (g : ℝ) : Finset ℤ :=
  (preferredMeanIndices N).filter (fun l => signedEqualityMean negative N l∈Icc (-d.b+g/4) B.delta)

/-- A source-specific partition using only genuinely regular equality
centers. The remaining complete density is supported at diameter≥r>0;
no analyticity is assumed at any excluded mean label. -/
theorem exists_regular_signed_finite_partition_germ {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {M : ℕ} (hM : 0<M)
    (d : PreferredBranchData)
    (hb : d.b=Real.arccos (|2*Real.cos (angle p a)|-1)) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump d,∀ negative : Bool,
      ∀ n : ℕ,n+1≤M → ∀ δB : ℝ,δB<B.delta → δB≤g/4 →
      ∀ R : ℤ → ℝ,(∀ l∈regularSignedMeanIndices d B negative (n+1) g,0<R l) →
      ∃ P : List ((Fin n → ℝ) → ℝ), ∃ rem : (Fin n → ℝ) → ℝ,∃ r : ℝ,
      0<r ∧ ContDiff ℝ ∞ rem ∧
      (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        ∃ l∈regularSignedMeanIndices d B negative (n+1) g,
          tsupport ψ⊆ball (fun _ => signedEqualityMean negative (n+1) l) (R l)) ∧
      (∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB → rem θ≠0 →
        r<preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB →
        preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))<r →
        rem =ᶠ[𝓝 θ] (fun _ => 0)) := by
  classical
  obtain ⟨g,hg,hcover⟩ := finite_signed_regular_center_cover hp hp5 ha hM d hb
  refine ⟨g,hg,?_⟩
  intro B negative n hn δB hδB hδ R hR
  let S := regularSignedMeanIndices d B negative (n+1) g
  let center (l : ℤ) : Fin n → ℝ := fun _ => signedEqualityMean negative (n+1) l
  obtain ⟨χ,ρ,hρ,hχ,hunit⟩ := exists_finite_center_cutoffs S center R hR
  let L := S.toList
  let r := min ρ (g/4)
  have hr : 0<r := lt_min hρ (by positivity)
  have hL (l : ℤ) : l∈L ↔ l∈S := Finset.mem_toList
  refine ⟨chartPartition χ L,chartRemainder χ L,r,hr,
    chartRemainder_contDiff χ L (fun l hl => (hχ l ((hL l).mp hl)).1),?_,
    chartPartition_identity χ L,?_⟩
  · intro ψ hψ
    obtain ⟨l,hl,hs⟩ := chartPartition_support χ L hψ
    have ht : tsupport ψ⊆tsupport (χ l) := closure_mono hs
    have hcl := hχ l ((hL l).mp hl)
    exact ⟨chartPartition_contDiff χ L (fun j hj => (hχ j ((hL j).mp hj)).1) ψ hψ,
      hcl.2.1.of_isClosed_subset (isClosed_tsupport ψ) ht,l,(hL l).mp hl,ht.trans hcl.2.2.2⟩
  · constructor
    · intro θ hθ hrem
      by_contra hh
      have hD := le_of_not_gt hh
      obtain ⟨l,hl,hreg,hs,hw⟩ := hcover B negative n hn δB hδB hδ θ hθ
        (hD.trans (min_le_right _ _))
      have hlS : l∈S := Finset.mem_filter.mpr ⟨hl,hreg⟩
      have hnorm : ‖θ-center l‖≤ρ := by
        apply (pi_norm_le_iff_of_nonneg hρ.le).mpr
        intro j
        have hj := hw j.castSucc
        rw [signed_lift_free_eq_of_right d B hδB (Physical.constraintAngle negative) θ hθ.1 hθ.2 j] at hj
        simpa only [Pi.sub_apply,Real.norm_eq_abs,center] using hj.trans (hD.trans (min_le_left _ _))
      exact hrem (chartRemainder_zero χ L ((hL l).mpr hlS) (hunit l hlS θ hnorm))
    · intro θ hθ hD
      obtain ⟨l,hl,hreg,hs,hw⟩ := hcover B negative n hn δB hδB hδ θ hθ
        (hD.le.trans (min_le_right _ _))
      have hlS : l∈S := Finset.mem_filter.mpr ⟨hl,hreg⟩
      have hnorm : ‖θ-center l‖<ρ := by
        have hn : ‖θ-center l‖≤preferredAngularDiameter
            (preferredLiftedAngles B.delta (constrainedAtTotal (Physical.constraintAngle negative) θ)) := by
          apply (pi_norm_le_iff_of_nonneg (Metric.diam_nonneg)).mpr
          intro j
          have hj := hw j.castSucc
          rw [signed_lift_free_eq_of_right d B hδB (Physical.constraintAngle negative) θ hθ.1 hθ.2 j] at hj
          simpa only [Pi.sub_apply,Real.norm_eq_abs,center,preferredAngularDiameter] using hj
        exact hn.trans_lt (hD.trans_le (min_le_left _ _))
      have hev : ∀ᶠ x in 𝓝 θ,‖x-center l‖<ρ :=
        (isOpen_ball.mem_nhds (show θ∈ball (center l) ρ by simpa only [mem_ball,dist_eq_norm] using hnorm))
      filter_upwards [hev] with x hx
      exact chartRemainder_zero χ L ((hL l).mpr hlS) (hunit l hlS x hx.le)

theorem exists_regular_signed_finite_partition {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {M : ℕ} (hM : 0<M)
    (d : PreferredBranchData)
    (hb : d.b=Real.arccos (|2*Real.cos (angle p a)|-1)) :
    ∃ g : ℝ,0<g ∧ ∀ B : PreferredCoareaBump d,∀ negative : Bool,
      ∀ n : ℕ,n+1≤M → ∀ δB : ℝ,δB<B.delta → δB≤g/4 →
      ∀ R : ℤ → ℝ,(∀ l∈regularSignedMeanIndices d B negative (n+1) g,0<R l) →
      ∃ P : List ((Fin n → ℝ) → ℝ), ∃ rem : (Fin n → ℝ) → ℝ,∃ r : ℝ,
      0<r ∧ ContDiff ℝ ∞ rem ∧
      (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        ∃ l∈regularSignedMeanIndices d B negative (n+1) g,
          tsupport ψ⊆ball (fun _ => signedEqualityMean negative (n+1) l) (R l)) ∧
      (∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion (Physical.constraintAngle negative) d B δB → rem θ≠0 →
        r<preferredAngularDiameter (preferredLiftedAngles B.delta
          (constrainedAtTotal (Physical.constraintAngle negative) θ))) := by
  obtain ⟨g,hg,hsource⟩ := exists_regular_signed_finite_partition_germ hp hp5 ha hM d hb
  refine ⟨g,hg,?_⟩
  intro B negative n hn δB hδB hδ R hR
  obtain ⟨P,rem,r,hr,hs,hP,hi,hfar,_hgerm⟩ := hsource B negative n hn δB hδB hδ R hR
  exact ⟨P,rem,r,hr,hs,hP,hi,hfar⟩

end
end IsingBulk.HT22.Geometry
