module
/- σ : type of data associated with each node
   ε : type of data associated with each edge
-/
public section
structure Node (σ ε : Type) where
  data : σ
  children : Array ε := #[]
