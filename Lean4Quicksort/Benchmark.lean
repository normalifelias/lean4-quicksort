import Std

@[noinline]
def sortIO [Ord α] [Inhabited α] (xs : Array α) (sort : Array α → Array α) : IO (Array α) := do --runs quicksort as IO function
  return sort xs

private def shuffle {α : Type u} (xs : Array α) (gen : StdGen) : Array α := -- shuffle an array by a random seed
  go xs gen 0
where
  go (xs : Array α) (gen : StdGen) (i : Nat) : Array α :=
    if _ : i < xs.size - 1 then
      let (j, gen) := randNat gen i (xs.size - 1)
      let xs := xs.swapIfInBounds i j
      go xs gen (i + 1)
    else
      xs

def index (n max : Nat) : String :=
  if max > 999 then
    (toString (n+1))
  else if max > 99 then
    if n < 9 then
      "00" ++ (toString (n+1))
    else
      if n < 99 then
        "0" ++ (toString (n+1))
      else
        (toString (n+1))
  else if max > 9 then
    if n < 9 then
      "0" ++ (toString (n+1))
    else
      (toString (n+1))
  else (toString (n+1))

def benchmark (tests n : Nat) (sort : Array Nat → Array Nat) : IO Unit := do -- run the IO quicksort with a shuffled array of size n
  let seed := UInt64.toNat (ByteArray.toUInt64LE! (← IO.getRandomBytes 8))
  let gen := mkStdGen seed
  let arr := Array.range n
  let shuffled := shuffle arr gen
  IO.println s!"╭─ benchmark"
  for i in 0...tests do
    let before ← Std.Time.Timestamp.now
    discard <| sortIO shuffled sort
    let duration ← before.since
    let dms := duration.toMilliseconds
    let mut ind := ""
    if dms <= 50 then ind := "★"
    else if dms < 100 then ind := "✔"
    else if dms < 200 then ind := "●"
    else if dms < 500 then ind := "⚠"
    else ind := "✖"
    IO.println s!"│ {index i tests} │ {dms}ms │ {ind}"
  IO.println s!"╰─"
  return ()
