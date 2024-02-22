include "../../Common/Native/NativeTypes.s.dfy"

abstract module AppInterface_s {
    import opened Native__NativeTypes_s

    type Key(==, !new)
    type Value

    predicate KeyLt(ka:Key, kb:Key) 

    lemma lemma_KeyOrdering()
        ensures forall k,k' :: KeyLt(k,k') ==> !KeyLt(k',k);                        // Antisymmetry
        ensures forall k,k' :: !KeyLt(k,k') ==> KeyLt(k',k) || k' == k;                        
        ensures forall k,k',k'' :: KeyLt(k,k') && KeyLt(k',k'') ==> KeyLt(k, k'');  // Transitivity

    function KeyMin() : Key
        ensures forall k :: k == KeyMin() || KeyLt(KeyMin(), k);

    ghost predicate ValidKey(key:Key)
    ghost predicate ValidValue(v:Value)

    ghost function MarshallSHTKey(k:Key) : seq<byte>
    ghost function MarshallSHTValue(v:Value) : seq<byte>
}
