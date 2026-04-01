-- import Lean4Quicksort.Basic
import Lean4Quicksort.Benchmark
import Lean4Quicksort.HiLo

def main : IO Unit := do
  let mut elements := 1000000
  while elements < 10000000 do
    IO.println "Ver 1"
    benchmark 2 elements quicksort
    IO.println "Ver 2"
    benchmark 2 elements quicksort2
    elements := elements * 2
