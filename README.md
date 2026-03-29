# lean4-quicksort

**(Lean4Quicksort.)HiLo.quicksort**  
Sorts a comparable array of any type efficiently by splitting it along a selected pivot
Usage: quicksort [array]

**(Lean4Quicksort.)Benchmark.benchmark**  
Runs a number of tests on a number of shuffled Nats with a selected algorithm, returns runtimes  
Usage: benchmark [number of tests] [number of elements] [target sorting algorithm]  
  
**Notes**  
  
- Basic.lean is slower than implementation from HiLo.lean and therefore deprecated
- Uses Array.swap or Array.set exclusively via [Dutch National Flag Problem](https://en.wikipedia.org/wiki/Dutch_national_flag_problem)
- Use true recursion on smaller returned stack from split
