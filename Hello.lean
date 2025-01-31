
def permutations {X : Type} (l : List X) : List (List X) :=
  let g p x := fun i => p.insertIdx i x
  let h x xs := fun p => List.map (g p x) (List.range (xs.length + 1))
  match l with
  | [] => [[]]
  | x :: xs => List.flatMap (permutations xs) (h x xs)

def allPermutations (n : Nat) : List (List Nat) :=
  permutations (List.range n)

def main : IO Unit := IO.println (allPermutations 6)
