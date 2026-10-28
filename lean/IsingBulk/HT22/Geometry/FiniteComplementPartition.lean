import IsingBulk.HT22.Geometry.FiniteEqualityCutoffs

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.Preferred22 IsingBulk.First LocalLimit
open scoped BigOperators Topology ContDiff

/-- An exact finite smooth partition of the original free-coordinate
integrand, with every local piece in a prescribed actual equality chart
and the entire remainder at a fixed positive angular diameter. -/
theorem exists_signed_finite_partition (n : ℕ) (a : ℝ) (ha : |a|≤Real.pi)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB : ℝ} (hδB : δB<B.delta)
    (R : ℤ → ℝ) (hR : ∀ l∈preferredMeanIndices (n+1),0<R l) :
    ∃ P : List ((Fin n → ℝ) → ℝ), ∃ rem : (Fin n → ℝ) → ℝ, ∃ r : ℝ,
      0<r ∧ ContDiff ℝ ∞ rem ∧
      (∀ ψ∈P,ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        ∃ l∈preferredMeanIndices (n+1),tsupport ψ ⊆
          ball (fun _ => (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)) (R l)) ∧
      (∀ θ, (P.map (fun ψ => ψ θ)).sum+rem θ=1) ∧
      (∀ θ : Fin n → ℝ,θ∈signedRightRegion a d B δB → rem θ≠0 →
        r<preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAtTotal a θ))) := by
  classical
  obtain ⟨χ,r,hr,hχ,hcover⟩ := exists_signed_equality_cutoffs n a ha d B hδB R hR
  let L := (preferredMeanIndices (n+1)).toList
  have hL (l : ℤ) : l∈L ↔ l∈preferredMeanIndices (n+1) := Finset.mem_toList
  refine ⟨chartPartition χ L,chartRemainder χ L,r,hr,
    chartRemainder_contDiff χ L (fun l hl => (hχ l ((hL l).mp hl)).1),?_,
    chartPartition_identity χ L,?_⟩
  · intro ψ hψ
    obtain ⟨l,hl,hs⟩ := chartPartition_support χ L hψ
    have ht : tsupport ψ ⊆ tsupport (χ l) := closure_mono hs
    have hcl := hχ l ((hL l).mp hl)
    refine ⟨chartPartition_contDiff χ L (fun j hj => (hχ j ((hL j).mp hj)).1) ψ hψ,
      hcl.2.1.of_isClosed_subset (isClosed_tsupport ψ) ht,l,(hL l).mp hl,ht.trans hcl.2.2.2⟩
  · intro θ hθ hrem
    by_contra hh
    obtain ⟨l,hl,hunit⟩ := hcover θ hθ (le_of_not_gt hh)
    exact hrem (chartRemainder_zero χ L ((hL l).mpr hl) hunit)

/-- The same exact partition acts on the complete complex density; no
local model or selected population replaces the coefficient. -/
theorem complete_density_partition {E : Type*} (P : List (E → ℝ)) (rem : E → ℝ)
    (hid : ∀ x,(P.map (fun ψ => ψ x)).sum+rem x=1) (F : E → ℂ) (x : E) :
    (P.map (fun ψ => (ψ x:ℂ)*F x)).sum+(rem x:ℂ)*F x=F x := by
  have he : (P.map (fun ψ => (ψ x:ℂ)*F x)).sum=
      (((P.map (fun ψ => ψ x)).sum:ℝ):ℂ)*F x := by
    clear hid
    induction P with
    | nil => simp
    | cons ψ P ih => simp only [List.map_cons,List.sum_cons,Complex.ofReal_add,add_mul,ih]
  rw [he,←add_mul,←Complex.ofReal_add,hid,Complex.ofReal_one,one_mul]

end
end IsingBulk.HT22.Geometry
