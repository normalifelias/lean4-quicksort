-- import Lean4Quicksort.Legacy
-- import Lean4Quicksort.V1
import Lean4Quicksort.V2
import Lean4Quicksort.Benchmark

-- V1: Uses a list of tasks (ranges) left to sort.
-- V2: Uses half-stack recursion. Also uses Vectors during sorting.
-- Legacy: Splits array into list of tasks, being either left to sort or ready to be pushed. Deprecated.

def main : IO Unit := do
  let runs := 3
  let elements := 1000000
  benchmark runs elements Array.qsortn "qsortn"
  benchmark runs elements Array.qsortOrdn "qsortOrdn"
  benchmark runs elements Array.qsort "qsort"
  benchmarkASC runs elements Array.qsortn "qsortn - asc"
  benchmarkASC runs elements Array.qsortOrdn "qsortOrdn - asc"
  benchmarkASC runs elements Array.qsort "qsort - asc"
  benchmarkDSC runs elements Array.qsortn "qsortn - dsc"
  benchmarkDSC runs elements Array.qsortOrdn "qsortOrdn - dsc"
  benchmarkDSC runs elements Array.qsort "qsort - dsc"
  benchmarkRPL runs elements Array.qsortn "qsortn- rpl"
  benchmarkRPL runs elements Array.qsortOrdn "qsortOrdn - rpl"
