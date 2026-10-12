import Ariadne.SourceFrom
import Ariadne.Shallow.Represents

namespace Ariadne.Shallow

/-- A data result is observed in the final source heap. Allocated objects and
borrowed references retain their actual runtime addresses. -/
def SourceRepresentsFrom (source name : String) (heap : Heap) (args : List Value)
    (layout : DataRelation Value α) (native : α) : Prop :=
  ∃ value after, SourceInvokes source {heap} (.function name) args value after ∧
    Represents layout after.heap value native

theorem transfer_represented {source : String} (certificate : Certificate source)
    {name : String} {heap : Heap} {args : List Value} {value : Value} {after : State}
    {layout : DataRelation Value α} {native : α} {footprint : Heap.Footprint}
    (invoked : Invokes certificate.program {heap} (.function name) args value after)
    (related : layout.Holds after.heap value native footprint) :
    SourceRepresentsFrom source name heap args layout native :=
  ⟨value, after, certificate.transfer_invocation invoked, footprint, related⟩

end Ariadne.Shallow
