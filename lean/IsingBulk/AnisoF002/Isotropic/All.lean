import IsingBulk.AnisoF002.Isotropic.BalancedContour
import IsingBulk.AnisoF002.Isotropic.CovarianceField
import IsingBulk.AnisoF002.Isotropic.VarianceCoercivity
import IsingBulk.AnisoF002.Isotropic.ProtectedVariance
import IsingBulk.AnisoF002.Isotropic.BalancedLipschitz
import IsingBulk.AnisoF002.Isotropic.OccupancyDerivative
import IsingBulk.AnisoF002.Isotropic.RegularInverse
import IsingBulk.AnisoF002.Isotropic.CellContraction
import IsingBulk.AnisoF002.Isotropic.TailSummation
import IsingBulk.AnisoF002.Isotropic.ScaleBudget

/-!
# New F002 isotropic partial development

This module collects checked local algebra, actual derivatives, finite-cell
contraction, and summation/scale arithmetic.  It contains no assertion of
complete differentiated tails, first-period noncancellation, the isotropic
natural boundary, or the final physical susceptibility theorem.
-/
