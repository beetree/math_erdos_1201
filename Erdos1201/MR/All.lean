import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Analysis.DiscreteMeanValue
import Erdos1201.MR.Analysis.DyadicPrimeSums
import Erdos1201.MR.Analysis.HalaszMontgomery
import Erdos1201.MR.Analysis.HilbertInequality
import Erdos1201.MR.Analysis.KusminLandau
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Analysis.PhaseSumDyadic
import Erdos1201.MR.Analysis.ShortRangePrimeMass
import Erdos1201.MR.Analysis.ShortRangePrimeMassBT
import Erdos1201.MR.Analysis.VanDerCorput
import Erdos1201.MR.Analysis.VanDerCorputIterated
import Erdos1201.MR.Analysis.VanDerCorputSubblock
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.WeylDifferencing
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Decomposition.Lemma12Assembly
import Erdos1201.MR.Decomposition.Lemma12Boundary
import Erdos1201.MR.Decomposition.Lemma12Square
import Erdos1201.MR.Decomposition.MediumAverage
import Erdos1201.MR.Exceptional
import Erdos1201.MR.Parseval.FourierAlias
import Erdos1201.MR.Parseval.HighFrequency
import Erdos1201.MR.Parseval.LowFrequency
import Erdos1201.MR.Parseval.PlancherelL1L2
import Erdos1201.MR.Parseval.SaffariVaughan
import Erdos1201.MR.Parseval.WindowKernel
import Erdos1201.MR.Parseval.WindowEnergy
import Erdos1201.MR.Parseval.WindowTransform
import Erdos1201.MR.Polynomials.DivisorMultiplicity
import Erdos1201.MR.Polynomials.MomentComputation
import Erdos1201.MR.Polynomials.PrimePolyMoments
import Erdos1201.MR.Polynomials.PrimePowerCoefficients
import Erdos1201.MR.Prop1.Split
import Erdos1201.MR.Ramare
import Erdos1201.MR.Ranges
import Erdos1201.MR.Setup
import Erdos1201.MR.ShortIntervalAssembly
import Erdos1201.MR.Sieve.InclusionExclusion
import Erdos1201.MR.Sieve.RangeSieveUpper
import Erdos1201.MR.Sieve.RangeSieveUpperHR
import Erdos1201.MR.Sieve.SiftedComplement
import Erdos1201.MR.Sieve.SmoothTail
import Erdos1201.MR.SupportReduction
import Erdos1201.MR.Target
import Erdos1201.MR.Twisted.TwistedChebyshev
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.MR.Vinogradov.FiniteFourier
import Erdos1201.MR.Vinogradov.HolderReduction
import Erdos1201.MR.Vinogradov.LinearBilinearSum
import Erdos1201.MR.Vinogradov.Linnik
import Erdos1201.MR.Vinogradov.PrimeSelection
import Erdos1201.MR.Vinogradov.PrimeSelectionMain
import Erdos1201.MR.Vinogradov.PrimeSelectionFinal3
import Erdos1201.MR.Vinogradov.PrimesInRange
import Erdos1201.MR.Vinogradov.PrimeSelectionAssembly
import Erdos1201.MR.Vinogradov.TaylorReduction
import Erdos1201.MR.Vinogradov.TaylorReductionMain
import Erdos1201.MR.Vinogradov.ZeroFreeGeneral
import Erdos1201.MR.Vinogradov.ZetaFromExpSums
import Erdos1201.MR.Parseval.Lemma14
import Erdos1201.MR.Prop1.E1
import Erdos1201.MR.Vinogradov.HolderRestriction
import Erdos1201.MR.Analysis.LogIteratedDifferences
import Erdos1201.MR.Analysis.VanDerCorputIteratedMain
import Erdos1201.MR.Vinogradov.CongruencingStep
import Erdos1201.MR.Twisted.TwistedContour
import Erdos1201.MR.Prop1.Ej
import Erdos1201.MR.Vinogradov.MeanValueTheorem
import Erdos1201.MR.Prop1.RPointwise
import Erdos1201.MR.Analysis.VanDerCorputSecondIterated
import Erdos1201.MR.Prop1.E1Unsifted
import Erdos1201.MR.Sieve.SmoothTailExp
import Erdos1201.MR.Analysis.VanDerCorputKth
import Erdos1201.MR.Prop1.UsetCard
import Erdos1201.MR.Prop1.UsetSmall
import Erdos1201.MR.Twisted.TwistedBounds
import Erdos1201.MR.Vinogradov.PrimeSelectionSq
import Erdos1201.MR.Twisted.TwistedPrimeSums
import Erdos1201.MR.Prop1.EjUnsifted
import Erdos1201.MR.Vinogradov.BilinearEstimate
import Erdos1201.MR.Prop1.RangeInstance
import Erdos1201.MR.Prop1.MomentBridge
import Erdos1201.MR.Analysis.HalaszPrimes

/-!
# Aggregator for the Matomäki–Radziwiłł formalization modules

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module imports every verified module of the in-progress formalization of the
Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4), so that `lake build`
checks them. Modules still under construction are not imported here.
-/
