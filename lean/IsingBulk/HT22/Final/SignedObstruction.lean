import IsingBulk.HT22.Final.SeriesSplit
import IsingBulk.HT22.Arithmetic.BranchCharts
import IsingBulk.HT.Final.RadialObstruction
import IsingBulk.HT.Final.DenseBoundary

/-! Honest signed-reflection transfer from the new positive-trace source
back to the original physical HT observable in either upper quadrant. -/
namespace IsingBulk.HT22.Final
noncomputable section
open IsingBulk.Final IsingBulk.HT.Final IsingBulk.HT22.Physical Arithmetic Filter Set
open scoped Topology

theorem no_extension_original_of_signed_negative {z : ℂ}
    (h : ¬HasExteriorExtension (signedOddSeries true) z) :
    ¬HasExteriorExtension oddSeries (-z) := by
  rintro ⟨U,hU,hzU,g,hg,hEq⟩
  apply h
  refine ⟨(fun s : ℂ => -s)⁻¹' U,hU.preimage continuous_neg,hzU,
    (fun s => -g (-s)),?_,?_⟩
  · intro s hs
    exact ((hg (-s) hs).comp analyticAt_id.neg).neg
  · intro s hs
    change -g (-s)=signedOddSeries true s
    have he := hEq (x := -s) ⟨hs.1,by simpa only [Set.mem_ofPred_eq,norm_neg] using hs.2⟩
    rw [he,signedOddSeries_negative hs.2]

theorem no_extension_original_of_effective_signed {α : ℝ}
    (h : ¬HasExteriorExtension (signedOddSeries (negativeSide α))
      (Complex.exp ((effectiveAngle α:ℂ)*Complex.I))) :
    ¬HasExteriorExtension oddSeries (Complex.exp ((α:ℂ)*Complex.I)) := by
  have hfalse : signedOddSeries false=oddSeries := funext signedOddSeries_positive
  by_cases hn : Real.pi/2<α
  · have hs : negativeSide α=true := by simp [negativeSide,hn]
    rw [effectiveAngle_root,hs] at h
    simp only [↓reduceIte] at h
    have hh := no_extension_original_of_signed_negative h
    rw [neg_neg] at hh
    have hc := no_extension_conjugate_of_real_symmetry
      (fun t ht => signedOddSeries_conjugate false ht) hh
    simpa only [hfalse,star_star] using hc
  · simpa only [negativeSide,decide_eq_false hn,effectiveAngle,ite_eq_right hn,
      hfalse] using h

end
end IsingBulk.HT22.Final
