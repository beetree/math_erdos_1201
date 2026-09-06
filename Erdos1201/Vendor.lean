import Erdos1201.Vendor.NumberTheory.HalberstamRichertMeanValue.ExplicitMeanValueBound
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.CosecantHilbert
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ConsecutiveInterval
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.FiniteDuality
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.MaximalBilinearLargeSieve
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.DirichletPerronSeries
import Erdos1201.Vendor.Analysis.GallagherSobolevPointwise
import Erdos1201.Vendor.Analysis.GallagherAdditiveLargeSievePrimal
import Erdos1201.Vendor.Analysis.DyadicBlockMultiplicityLargeSieve
import Erdos1201.Vendor.NumberTheory.PNT.MertensErrorTermAsymptotics
import Erdos1201.Vendor.NumberTheory.MertensTheorems
import Erdos1201.Vendor.NumberTheory.SelbergSieve.BrunTitchmarsh
import Erdos1201.Vendor.NumberTheory.Analytic.RoughCount
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroFreeRegionCapstone
import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
import Erdos1201.Vendor.NumberTheory.RandomMultiplicativeFunctions.PrimeCosineOscillationBound

/-!
# Vendored analytic number theory

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.

These modules are copied verbatim (module paths renamed) from the user's `solve-math`
corpus, which is pinned to the same Lean toolchain and Mathlib commit. They provide the
Montgomery–Vaughan Hilbert inequality and large sieve, Perron's formula, Mertens' theorems
with error terms, the Selberg sieve, the classical zero-free region, and the medium prime
number theorem, all used in the formalization of the Matomäki–Radziwiłł input.
-/
