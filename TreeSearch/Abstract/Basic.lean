module
/- σ : type of data associated with each node
   ε : type of data associated with each edge
-/
public section

namespace Reap.TreeSearch

structure Node (σ ε : Type) where
  data : σ
  children : Array ε := #[]

end Reap.TreeSearch
